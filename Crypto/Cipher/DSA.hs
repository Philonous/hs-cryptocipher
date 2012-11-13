-- |
-- Module      : Crypto.Cipher.DSA
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : Good
--

module Crypto.Cipher.DSA
	( Error(..)
	, Params
	, Signature
	, PublicKey(..)
	, PrivateKey(..)
	, sign
	, verify
	) where

import Crypto.Random
import Crypto.Types.PubKey.DSA
import Data.ByteString (ByteString)
import Data.Maybe (isNothing)
import Number.Generate
import Number.ModArithmetic (exponantiation, inverse)
import Number.Serialize

data Error =
	  InvalidSignature          -- ^ signature is not valid r or s is not between the bound 0..q
	| RandomGenFailure GenError -- ^ the random generator returns an error. give the opportunity to reseed for example.
        | ParameterError -- ^ q is not prime. Note that a composite q does not
                         -- necessarily lead to this error (e.g. when it's a
                         -- Carmichael number)
	deriving (Show,Eq)

{-| sign message using the private key. -}
sign :: CryptoRandomGen g => g -> (ByteString -> ByteString) -> PrivateKey -> ByteString -> Either Error (Signature, g)
sign rng hash pk m =
	-- Recalculate the signature in the unlikely case that r = 0 or s = 0
	case generateMax rng q of
		Left err        -> Left $ RandomGenFailure err
		Right (k, rng') -> do
			kinv <- maybe (Left ParameterError) Right $ inverse k q
			let r    = expmod g k p `mod` q
			let s    = (kinv * (hm + x * r)) `mod` q
			if r == 0 || s == 0
				then sign rng' hash pk m
				else Right ((r, s), rng')
	where
		(p,g,q)   = private_params pk
		x         = private_x pk
		hm        = os2ip $ hash m

{- | verify a bytestring using the public key. -}
verify :: Signature -> (ByteString -> ByteString) -> PublicKey -> ByteString -> Either Error Bool
verify (r,s) hash pk m
	-- Reject the signature if either 0 < r <q or 0 < s < q is not satisfied.
	| r <= 0 || r >= q || s <= 0 || s >= q = Left InvalidSignature
        | isNothing w'                         = Left ParameterError
	| otherwise                            = Right $ v == r
	where
		(p,g,q) = public_params pk
		y       = public_y pk
		hm      = os2ip $ hash m
		w'      = inverse s q
		w       = maybe (error "DSA.verify: inverse is Nothing") id w'
		u1      = (hm*w) `mod` q
		u2      = (r*w) `mod` q
		v       = ((expmod g u1 p) * (expmod y u2 p)) `mod` p `mod` q

expmod :: Integer -> Integer -> Integer -> Integer
expmod = exponantiation
