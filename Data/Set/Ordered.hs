{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

-- | An 'OSet' behaves much like a 'Set', with mostly the same asymptotics, but
-- also remembers the order that values were inserted (i.e., last in, first out).
-- All operations whose asymptotics are worse than 'Set' have documentation saying so.
module Data.Set.Ordered
	( OSet
	-- * Trivial sets
	, empty, singleton
	-- * Insertion
	-- | Conventions:
	--
	-- * The open side of an angle bracket points to an 'OSet'
	--
	-- * The pipe appears on the side whose indices take precedence for keys that appear on both sides
	--
	-- * The left argument's indices are lower than the right argument's indices
	, (<|), (|<), (>|), (|>)
	, (<>|), (|<>)
	, Bias(Bias, unbiased), L, R
	-- * Query
	, null, size, member, notMember
	-- * Deletion
	, delete, filter, (\\), (|/\), (/\|)
	-- * Indexing
	, Index, findIndex, elemAt
	-- * List conversions
	, fromList, toAscList
	-- * 'Set' conversion
	, toSet
	) where

import Control.Monad (guard)
import Data.Data
import Data.Foldable (Foldable, foldl', foldMap, foldr, toList)
import Data.Function (on)
import Data.Hashable (Hashable(..))
import Data.Map (Map)
import Data.Map.Util
import Data.Monoid (Monoid(..))
#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup(..))
#endif
import Data.Set (Set) -- so the haddocks link to the right place
import Prelude hiding (filter, foldr, lookup, null)
import qualified Data.Map as M
import qualified GHC.Exts as Exts

data OSet a = OSet !(Map a Tag) !(Map Tag a)
	deriving Typeable -- ^ @since 0.2

-- | Values appear in insertion order, not ascending order.
instance Foldable OSet where foldMap f (OSet _ vs) = foldMap f vs
instance         Eq   a  => Eq   (OSet a) where (==)    = (==)    `on` toList
instance         Ord  a  => Ord  (OSet a) where compare = compare `on` toList
instance         Show a  => Show (OSet a) where showsPrec = showsPrecList toList
instance (Ord a, Read a) => Read (OSet a) where readsPrec = readsPrecList fromList
-- | @since 0.2.4
instance     Hashable a  => Hashable (OSet a) where hashWithSalt s = hashWithSalt s . toList

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.
-- | @since 0.2
instance (Data a, Ord a) => Data (OSet a) where
	gfoldl f z set = z fromList `f` toList set
	toConstr _     = fromListConstr
	gunfold k z c  = case constrIndex c of
		1 -> k (z fromList)
		_ -> error "gunfold"
	dataTypeOf _   = oSetDataType
	-- dataCast1 /must/ be eta-expanded in order to build on GHC 7.8.
	dataCast1 f    = gcast1 f

fromListConstr :: Constr
fromListConstr = mkConstr oSetDataType "fromList" [] Prefix

oSetDataType :: DataType
oSetDataType = mkDataType "Data.Set.Ordered.Set" [fromListConstr]

-- | @'GHC.Exts.fromList' = 'fromList'@ and @'GHC.Exts.toList' = 'toList'@.
--
-- @since 0.2.4
instance Ord a => Exts.IsList (OSet a) where
	type Item (OSet a) = a
	fromList = fromList
	toList = toList

#if MIN_VERSION_base(4,9,0)
-- | @since 0.2
instance Ord a => Semigroup (Bias L (OSet a)) where Bias o <> Bias o' = Bias (o |<> o')
-- | @since 0.2
instance Ord a => Semigroup (Bias R (OSet a)) where Bias o <> Bias o' = Bias (o <>| o')
#endif

-- | Empty sets and set union. When combining two sets that share elements, the
-- indices of the left argument are preferred.
--
-- See the asymptotics of ('|<>').
--
-- @since 0.2
instance Ord a => Monoid (Bias L (OSet a)) where
	mempty = Bias empty
	mappend (Bias o) (Bias o') = Bias (o |<> o')

-- | Empty sets and set union. When combining two sets that share elements, the
-- indices of the right argument are preferred.
--
-- See the asymptotics of ('<>|').
--
-- @since 0.2
instance Ord a => Monoid (Bias R (OSet a)) where
	mempty = Bias empty
	mappend (Bias o) (Bias o') = Bias (o <>| o')

infixr 5 <|, |<   -- copy :
infixl 5 >|, |>
infixr 6 <>|, |<> -- copy <>

(<|) , (|<)  :: Ord a =>      a -> OSet a -> OSet a
(>|) , (|>)  :: Ord a => OSet a ->      a -> OSet a

-- | /O(m*log(n)+n)/, where /m/ is the size of the smaller set and /n/ is the
-- size of the larger set.
(<>|) :: Ord a => OSet a -> OSet a -> OSet a

-- | /O(m*log(n)+n)/, where /m/ is the size of the smaller set and /n/ is the
-- size of the larger set.
(|<>) :: Ord a => OSet a -> OSet a -> OSet a

v <| o@(OSet ts vs)
	| v `member` o = o
	| otherwise    = OSet (M.insert v t ts) (M.insert t v vs) where
		t = nextLowerTag vs

v |< o = OSet (M.insert v t ts) (M.insert t v vs) where
	t = nextLowerTag vs
	OSet ts vs = delete v o

o@(OSet ts vs) |> v
	| v `member` o = o
	| otherwise    = OSet (M.insert v t ts) (M.insert t v vs) where
		t = nextHigherTag vs

o >| v = OSet (M.insert v t ts) (M.insert t v vs) where
	t = nextHigherTag vs
	OSet ts vs = delete v o

o <>| o' = unsafeMappend (o \\ o') o'
o |<> o' = unsafeMappend o (o' \\ o)

-- assumes that ts and ts' have disjoint keys
unsafeMappend (OSet ts vs) (OSet ts' vs')
	= OSet (M.union tsBumped tsBumped')
	       (M.union vsBumped vsBumped')
	where
	bump  = case maxTag vs  of
		Nothing -> 0
		Just k  -> -k-1
	bump' = case minTag vs' of
		Nothing -> 0
		Just k  -> -k
	tsBumped  = fmap (bump +) ts
	tsBumped' = fmap (bump'+) ts'
	vsBumped  = (bump +) `M.mapKeysMonotonic` vs
	vsBumped' = (bump'+) `M.mapKeysMonotonic` vs'

-- | Set difference: @r \\\\ s@ deletes all the values in @s@ from @r@. The
-- order of @r@ is unchanged.
--
-- /O(m*log(n))/ where /m/ is the size of the smaller set and /n/ is the size
-- of the larger set.
(\\) :: Ord a => OSet a -> OSet a -> OSet a
o@(OSet ts vs) \\ o'@(OSet ts' vs') = if size o < size o'
	then filter (`notMember` o') o
	else foldr delete o vs'

-- | Intersection. (@/\\@ is meant to look a bit like the standard mathematical
-- notation for intersection.)
--
-- /O(m*log(n\/(m+1)) + r*log(r))/, where /m/ is the size of the smaller set,
-- /n/ the size of the larger set, and /r/ the size of the result.
--
-- @since 0.2
(|/\) :: Ord a => OSet a -> OSet a -> OSet a
OSet ts vs |/\ OSet ts' vs' = OSet ts'' vs'' where
	ts'' = M.intersection ts ts'
	vs'' = M.fromList [(t, v) | (v, t) <- M.toList ts'']

-- | @flip ('|/\')@
--
-- See asymptotics of '|/\'.
--
-- @since 0.2
(/\|) :: Ord a => OSet a -> OSet a -> OSet a
(/\|) = flip (|/\)

empty :: OSet a
empty = OSet M.empty M.empty

member, notMember :: Ord a => a -> OSet a -> Bool
member    v (OSet ts _) = M.member    v ts
notMember v (OSet ts _) = M.notMember v ts

size :: OSet a -> Int
size (OSet ts _) = M.size ts

-- the Ord constraint is for compatibility with older (<0.5) versions of
-- containers
filter :: Ord a => (a -> Bool) -> OSet a -> OSet a
filter f (OSet ts vs) = OSet (M.filterWithKey (\v t -> f v) ts)
                             (M.filterWithKey (\t v -> f v) vs)

delete :: Ord a => a -> OSet a -> OSet a
delete v o@(OSet ts vs) = case M.lookup v ts of
	Nothing -> o
	Just t  -> OSet (M.delete v ts) (M.delete t vs)

singleton :: a -> OSet a
singleton v = OSet (M.singleton v 0) (M.singleton 0 v)

-- | If a value occurs multiple times, only the first occurrence is used.
fromList :: Ord a => [a] -> OSet a
fromList = foldl' (|>) empty

null :: OSet a -> Bool
null (OSet ts _) = M.null ts

findIndex :: Ord a => a -> OSet a -> Maybe Index
findIndex v o@(OSet ts vs) = do
	t <- M.lookup v ts
	M.lookupIndex t vs

elemAt :: OSet a -> Index -> Maybe a
elemAt o@(OSet ts vs) i = do
	guard (0 <= i && i < M.size vs)
	return . snd $ M.elemAt i vs

-- | Returns values in ascending order. (Use 'toList' to return them in
-- insertion order.)
toAscList :: OSet a -> [a]
toAscList o@(OSet ts _) = fmap fst (M.toAscList ts)

-- | Convert an 'OSet' to a 'Set'.
--
-- /O(n)/, where /n/ is the size of the 'OSet'.
--
-- @since 0.2.2
toSet :: OSet a -> Set a
toSet (OSet ts _) = M.keysSet ts
