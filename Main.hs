{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}

-- | A verbose decoder for flat encoding of de Bruijn-indexed Untyped Plutus
-- Core programs.  This is intentionally simplistic to make it clear what's
-- going on.

module Main where

import           Codec.Serialise      (deserialise)
import           Data (Data (..))
import qualified Data as D
import           Data.Bits
import           Data.ByteString.Lazy as BSL (ByteString, foldr, pack, readFile,
                                              toStrict, unpack)
import qualified Data.ByteString.Lazy as BSL (fromStrict, length)
import           Data.Char            (chr)
import           Data.Text            (Text)
import           Data.Text.Encoding   (decodeUtf8')
import           Data.Word
-- import           Debug.Trace          (trace)
import           Numeric              (showHex)
import           System.Environment   (getArgs)
import           Text.Printf          (printf)


-- Input buffer: ptr = curent bit (8..1), hd = first byte, rest = remaining
-- bytes, offset = number of bits read so far.
data Input =
    Input {ptr :: Int, hd :: Word8, rest :: [Word8], offset :: Integer}
    deriving Show

stringOfOffset :: Input -> String
stringOfOffset (Input p _ _ o) = printf "bit %d of byte %d" p (o `div` 8)

-- For incrementing offsets
addTo :: Integral a => Integer -> a -> Integer
addTo n k = n + fromIntegral k

filler :: String
filler = "         *"

endOfInput :: Input -> Bool
endOfInput (Input p _ r _) =
    p==0 && r==[]

constantWidth :: Int
constantWidth = 4

termTagWidth :: Int
termTagWidth = 4

typeTagWidth :: Int
typeTagWidth = 4

builtinTagWidth :: Int
builtinTagWidth = 7

builtins :: [String]
builtins =
    [ "addInteger", "subtractInteger", "multiplyInteger", "divideInteger", "quotientInteger",
      "remainderInteger", "modInteger", "equalsInteger", "lessThanInteger", "lessThanEqualsInteger",
      "appendByteString", "consByteString", "sliceByteString", "lengthOfByteString", "indexByteString",
      "equalsByteString", "lessThanByteString", "lessThanEqualsByteString", "sha2_256", "sha3_256",
      "blake2b_256", "verifyEd25519Signature", "appendString", "equalsString", "encodeUtf8",
      "decodeUtf8", "ifThenElse", "chooseUnit", "trace", "fstPair",
      "sndPair", "chooseList", "mkCons", "headList", "tailList",
      "nullList", "chooseData", "constrData", "mapData", "listData",
      "iData", "bData", "unConstrData", "unMapData", "unListData",
      "unIData", "unBData", "equalsData", "mkPairData", "mkNilData",
      "mkNilPairData", "serialiseData", "verifyEcdsaSecp256k1Signature", "verifySchnorrSecp256k1Signature",
      "bls12_381_G1_add", "bls12_381_G1_mul", "bls12_381_G1_neg", "bls12_381_G1_equal", "bls12_381_G1_compress",
      "bls12_381_G1_uncompress", "bls12_381_G1_hashToCurve", "bls12_381_G2_add", "bls12_381_G2_mul",
      "bls12_381_G2_neg", "bls12_381_G2_equal", "bls12_381_G2_compress", "bls12_381_G2_uncompress",
      "bls12_381_G2_hashToCurve", "bls12_381_GT_mul", "bls12_381_GT_finalVerify", "bls12_381_GT_millerLoop",
      "keccak_256", "blake2b_224"
    ]

-- Convert an integer into a binary string of length n
bitsToString :: Int -> Integer -> String
bitsToString n b =
    if b >= (1 `shift` (n+1))
    then error $ printf "bitsToString: %d is more than %d bits long" b n
    else go n
        where go j =
                  if j==0 then []
                  else let bit = (1 `shift` (j-1)) .&. b
                       in if bit == 0
                          then '0' : go (j-1)
                          else '1' : go (j-1)

bitsToString8 :: Int -> Word8 -> String
bitsToString8 n w = bitsToString n (fromIntegral w)

mask :: Int -> Word8 -> Word8
mask n w =
    let m = case n of
              0 -> 0x00
              1 -> 0x01
              2 -> 0x03
              3 -> 0x07
              4 -> 0x0f
              5 -> 0x1f
              6 -> 0x3f
              7 -> 0x7f
              8 -> 0xff
              _ -> error $ printf "Mask width too big: %d" n
    in w .&. m

-- Check that if we discard the bits before the p-th one, we're left with 0...01
checkPadding :: Input -> IO ()
checkPadding i@(Input p h _ _) =
    if mask p h == 1
    then pure ()
    else error $ printf "Unexpected padding %s at offset %s" (bitsToString8 p h) (stringOfOffset i)

getBits :: Int -> Input -> (Integer, Input)
getBits n0 (Input p0 h0 r0 offset) =
    let (p1, h1, r1, acc1) =
            if p0 == 0
            then case r0 of
                   []   -> error $ printf "Attempted to read %d bits from empty buffer" n0
                   w:ws -> get n0 (8, w, ws, 0)
            else get n0 (p0, h0, r0, 0)
    in (acc1, Input p1 h1 r1 (addTo offset n0))
        where get n (y@(p, h, r, acc)) =
                  if n==0
                  then (p, h, r, acc)
                  else get (n-1) (get1Bit y)
              get1Bit (p, h, r, acc) =
                  if p == 0 then
                      case r of
                        []   -> error "Ran out of input"
                        w:ws -> get1Bit (8, w, ws, acc)
                  else let
                      p' = p-1
                      h' = mask (p-1) h
                      acc' = (acc `shift` 1) .|. fromIntegral (h `shift` (1-p) .&. 1)
                 in (p', h', r, acc')

decodeBuiltinName :: Input -> IO (String, Input)
decodeBuiltinName i  =
    let (tag, i1) = getBits builtinTagWidth i
        tag' = fromIntegral tag
    in if tag' < length builtins
       then do
         printf "%-8s : builtin tag %d\n" (bitsToString builtinTagWidth tag) tag'
         pure (builtins !! tag', i1)
       else error $ printf "At %s: failed to decode builtin tag (got %d)" (stringOfOffset i) tag'


-- Drop any remaining bits in the current byte.
-- If we're at the end of the current byte, drop the whole of the next byte.
-- Check that all filler is of the expected form: 0....01
dropPadding :: Input -> IO Input
dropPadding i@(Input p h r offset) =
    if p == 0
    then case r of
           []   -> error "End of input, but expected padding"
           w:ws -> dropPadding $ Input 8 w ws offset -- Advance to the next byte
    else do
      checkPadding i
      printf "%-8s : padding\n" (bitsToString p (fromIntegral h))
      case r of
        []    -> pure $ Input 0 0 [] offset  -- Fake input for end of data
        h1:rs ->
            pure $ Input 8 h1 rs (addTo offset p) -- Advance to next byte

toHex2 :: Word8 -> String
toHex2 w = if w <=15
           then "0" ++ showHex w ""
           else showHex w ""
toHexString :: ByteString -> String
toHexString = BSL.foldr (\b -> (++) (toHex2 b)) ""

-- See the comments in Flat.Instances.ByteString
decodeByteString :: Input -> IO (ByteString, Input)
decodeByteString i0 = do
  i1 <- dropPadding i0
  (bytes, i2) <- getBytes i1
  let bs = pack bytes
  pure (bs, i2)
  where getBytes i =
            let (blockSize, j) = getBits 8 i
            in do
              printf "%-8s : bytestring block size: %d\n" (bitsToString 8 blockSize) blockSize
              if blockSize == 0
               then pure ([],j)
               else do
                 (bytes, j') <- getNBytes blockSize j
                 (rest, j'') <- getBytes j'
                 pure (bytes ++ rest, j'')
        getNBytes :: Integer -> Input -> IO ([Word8], Input)
        getNBytes n i =
            if n==0
            then pure ([],i)
            else do
              let (b, i') =  getBits 8 i
              printf "%-8s : 0x%s  %s\n"
                         (bitsToString 8 b)
                         (toHex2 (fromIntegral b :: Word8))
                         (show $ chr (fromIntegral b :: Int))
              (a, i'') <- getNBytes (n-1) i'
              pure $ ((fromIntegral b):a, i'')

decodeText :: Input -> IO (Text, Input)
decodeText i0 = do
  (bytes, i1) <- decodeByteString i0
  printf "%s [Text] # %s\n" filler (toHexString bytes)
  case decodeUtf8' (toStrict bytes) of
    Left err   -> error $ printf "decodeUtf8 failed at %s: %s" (stringOfOffset i0) (show err)
    Right text -> pure (text, i1)

decodeData :: Input -> IO (ByteString, Input)
decodeData = decodeByteString

-- Divide input into 7-bit chunks, prefix chunk with 1 if more to come, 0 if no
-- more.  Start at the RIGHT: the first 1+7 bits in the output represent the
-- last (rightmost) 7 bits in the input.
decodeBitString :: Input -> IO (Integer, Input)
decodeBitString i0 =
    decode i0 0 0
    where decode i acc sh = do
            let (h, i') = getBits 8 i
                acc' = (fromIntegral (h .&. 0x7F) `shift` sh) .|. acc
            printf "%-8s : bitstring chunk\n" (bitsToString 8 h)
            if (h .&. 0x80) == 0x80  -- More data
            then decode  i' acc' (sh+7)
            else pure (acc', i')

decodeNat :: Input -> IO (Integer, Input)
decodeNat i = do
  (n,i') <- decodeBitString i
  printf "%s Nat: %d\n" filler n
  pure (n,i')

-- zigzag encoding: 0 -> 0, 1 -> -1, 2 -> 1, 3 -> -2, 4 -> 2, ...
-- if n is even then n/2, else -(n-1)/2 - 1
decodeInteger :: Input -> IO (Integer, Input)
decodeInteger i = do
  (n,i') <- decodeBitString i
  let m = if n .&. 1 == 1
          then -(n `shift` (-1)) - 1  -- negative
          else  n `shift` (-1)        -- positive
  pure (m,i')


decodeBool :: Input -> IO (Bool, Input)
decodeBool i = do
    let (v,i1) = getBits 1 i
        b = case v of
              0 -> False
              1 -> True
              _ -> error $ printf "Invalid bool tag %d at %s" v (stringOfOffset i)
    printf "%-8s : boolean value\n" (bitsToString 1 v)
    pure (b,i1)


decodeWord64 :: Input -> IO Input
decodeWord64 i = do
    let (v,i1) = getBits 8 i
    printf "%-8s : Word64 %d\n" (bitsToString 8 v) v
    pure i1


getTagList :: Input -> Int -> IO ([Integer], Input)
getTagList i0 width =
    get i0
        where get i = do
                  let (b,i1) = getBits 1 i
                  if b == 0
                  then do
                    printf "%-8s : end of list\n" ("0"::String)
                    pure ([],i1)
                  else do
                    printf "%-8s : list entry\n" ("1"::String)
                    let (n, i2) = getBits width i1
                    printf "%-8s : %d\n" (bitsToString width n) n
                    (l, i3) <- get i2
                    pure (n:l, i3)

-- decodeType :: Input -> IO ([Integer], Input)
-- decodeType i = do
--   (l, i') <- getTagList 4 i
--   printf "Type: "
--   pure (l,i')

printBlengths :: Data -> IO ()
printBlengths x = case x of
    Constr _ l -> mapM_ printBlengths l
    Map l      -> mapM_ (\(x,y) -> printBlengths x >> printBlengths y) l
    List l     -> mapM_ printBlengths l
    I _        -> pure ()
    B b        -> printf "### %d bytes\n" (BSL.length $ BSL.fromStrict b)


data Type
    = TypeInteger              -- 0
    | TypeByteString           -- 1
    | TypeString               -- 2
    | TypeUnit                 -- 3
    | TypeBool                 -- 4
    | TypeList Type            -- 5
    | TypePair Type Type       -- 6
    | TypeData                 -- 8
    | TypeBLS12_381_G1_Element -- 9
    | TypeBLS12_381_G2_Element -- 10
    | TypeBLS12_381_MlResult   -- 11


instance Show Type where
    show TypeInteger              = "integer"
    show TypeByteString           = "bytestring"
    show TypeString               = "string"
    show TypeUnit                 = "unit"
    show TypeBool                 = "bool"
    show (TypeList ty)            = printf "list(%s)" (show ty)
    show (TypePair ty1 ty2)       = printf "pair(%s,%s)" (show ty1) (show ty2)
    show TypeData                 = "data"
    show TypeBLS12_381_G1_Element = "bls12_381_G1_element"
    show TypeBLS12_381_G2_Element = "bls12_381_G2_element"
    show TypeBLS12_381_MlResult   = "bls12_381_mlresult"

parseTypeTags :: Input -> [Integer] -> Type
parseTypeTags i l =
    let getTypes =
            \case
                 []         -> error $ printf "Empty type tag list at %s" off
                 0:tags     -> (TypeInteger, tags)
                 1:tags     -> (TypeByteString, tags)
                 2:tags     -> (TypeString, tags)
                 3:tags     -> (TypeUnit, tags)
                 4:tags     -> (TypeBool, tags)
                 7:5:tags   -> let (ty, tags') = getTypes tags  -- List
                               in (TypeList ty, tags')
                 7:7:6:tags -> let (ty1, tags1) = getTypes tags  --- Pair
                                   (ty2, tags2) = getTypes tags1
                               in (TypePair ty1 ty2, tags2)
                 8:tags     -> (TypeData, tags)
                 9:tags     -> (TypeBLS12_381_G1_Element, tags)
                 10:tags    -> (TypeBLS12_381_G2_Element, tags)
                 11:tags    -> (TypeBLS12_381_MlResult, tags)
                 t:_        -> error $ printf "Unexpected type tag %d at %s (tags = %s)" t off (show l)
    in case getTypes l
       of (t,[]) -> t
          (t,extra) -> error $ printf "Found extra type tags after %s: %s (%s)" (show t) (show extra) off
    where off = stringOfOffset i  -- May be imprecise

{- Tag 7: Apply type to type
[7,5,4] -> app list bool
[7,5,2] -> app list string
[7,7,6,4,2] -> app (app pair bool) string
[7,7,6,7,7,6,0,3,7,5,2] (app (app pair (app (app pair integer) unit) (app list string)))
                        pair (pair integer unit) (list string)

-}

decodeConstantList :: Input -> Type -> IO Input
decodeConstantList i0 ty = get i0
    where get i = do
            let (b,i1) = getBits 1 i
            if b == 0
            then do
              printf "%-8s : end of list\n" ("0"::String)
              pure i1
            else do
              printf "%-8s : list entry\n" ("1"::String)
              i2 <- decodeConstantVal i1 ty
              decodeConstantList i2 ty

decodeConstantVal :: Input -> Type -> IO Input
decodeConstantVal i ty =
    case ty of
      TypeInteger -> do
        (n, i1) <- decodeInteger i
        printf "%s con integer %d\n" filler n
        pure i1
      TypeByteString -> do
        (bs, i1) <- decodeByteString i
        printf "%s con bytestring # %s\n" filler (toHexString bs)
        pure i1
      TypeString -> do
        (s, i1) <- decodeText i
        printf "%s con string \"%s\"\n" filler s
        pure i1
      TypeUnit -> do
        printf "%s con unit ()\n" filler
        pure i
      TypeBool -> do
        (b, i1) <- decodeBool i
        printf "%s con bool %s\n" filler (show b)
        pure i1
      TypeList ty -> do
        i1 <- decodeConstantList i ty
        -- What happens if we lie about the types of the list elements?  An unlifting error?
        pure i1
      TypePair t1 t2 -> do
        i1 <- decodeConstantVal i t1
        i2 <- decodeConstantVal i1 t2
        pure i2
      TypeData -> do
        (d,i1) <- decodeData i
        printf "%s con data # %s\n" filler (toHexString d)
        let d2 = deserialise d :: Data
        putStrLn $ D.toString d2
        pure i1
      TypeBLS12_381_G1_Element -> do
              (b,i1) <- decodeByteString i
              printf "%s con bls12_381_G1_element 0x%s\n" filler (toHexString b)
              pure i1
      TypeBLS12_381_G2_Element -> do
              (b,i1) <- decodeByteString i
              printf "%s con bls12_381_G2_element 0x%s\n" filler (toHexString b)
              pure i1
      TypeBLS12_381_MlResult -> error "Unexpected value of type bls12_381_mlresult"

decodeConstant :: Input -> IO Input
decodeConstant i = do
    (tags, i1) <- getTagList i typeTagWidth
    printf "%s type tags: %s\n" filler (show tags)
    let ty = parseTypeTags i1 tags  -- i1 is just fed to parseTypeTags for position information
    printf "%s type: %s\n" filler (show ty)
    decodeConstantVal i1 ty

decodeTermList :: Input -> IO Input
decodeTermList i0 = get i0
    where get i = do
            let (b,i1) = getBits 1 i
            if b == 0
            then do
              printf "%-8s : end of list\n" ("0"::String)
              pure i1
            else do
              printf "%-8s : list entry\n" ("1"::String)
              i2 <- decodeTerm i1
              decodeTermList i2

decodeTerm :: Input -> IO Input
decodeTerm i =
    if endOfInput i
    then
        error "End of input while trying to decode term"
    else do
      let (tag, i1) = getBits termTagWidth i
      printf "%-8s : " (bitsToString termTagWidth tag)
      case tag of
         0 -> do   -- var
           printf "var\n"
           (index, i2) <- decodeNat i1
           printf "%s index %d\n" filler index
           pure i2
         1 -> do    -- delay
           printf "delay\n"
           decodeTerm i1
         2 -> do    -- lam
           printf "lam (deBruijn)\n"  -- No variable
           decodeTerm i1
         3 -> do   -- apply
           printf "apply\n"
           i2 <- decodeTerm i1
           i3 <- decodeTerm i2
           pure i3
         4 -> do   -- constant
             printf "constant\n"
             i2 <- decodeConstant i1
             pure i2
         5 -> do   -- force
           printf "force\n"
           i2 <- decodeTerm i1
           pure i2
         6 -> do   -- error
             printf "error\n" >> pure i1
         7 -> do   -- builtin
           printf "builtin\n"
           (b, i2) <- decodeBuiltinName i1
           printf "%s builtin %s\n" filler b
           pure i2
         8 -> do  -- constr  ann Word64 [Term]
           printf "constr\n"
           i2 <- decodeWord64 i1
           i3 <- decodeTermList i2
           pure i3
         9 -> do  -- case ann Term [Term]
           printf "case\n"
           i2 <- decodeTerm i1
           i3 <- decodeTermList i2
           pure i3
         n -> error $ printf "Invalid term tag %d at %s" n (stringOfOffset i1) -- Should be impossible

decodeProg :: [Word8] -> IO ()
decodeProg b = do
--  mapM_ (\n -> printf "0x%02x\n" n) b
  let input = Input 0 0 b 0
  (v1,i1) <- decodeNat input
  (v2,i2) <- decodeNat i1
  (v3,i3) <- decodeNat i2
  printf "%s Version: %d.%d.%d\n" filler v1 v2 v3
  i@(Input _ _ r _) <- decodeTerm i3 >>= dropPadding
  if endOfInput i
  then pure ()
  else printf "Unused input: %s\n" (show r)
  printf "** END **\n"

main :: IO ()
main = do
    args <- getArgs
    case args of
      []     -> putStrLn "Filename expected"
      [file] -> (BSL.unpack <$> BSL.readFile file) >>= decodeProg
      _      -> putStrLn "Too many arguments: extected a filename"
