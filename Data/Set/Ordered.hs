-- | An 'OSet' behaves much like a 'Set', with all the same asymptotics, but
-- also remembers the order that values were inserted.
module Data.Set.Ordered
	( OSet
	-- * Trivial sets
	, empty, singleton
	-- * Insertion
	-- | Conventionts:
	--
	-- * The open side of an angle bracket points to an 'OSet'
	--
	-- * The pipe appears on the side whose indices take precedence for keys that appear on both sides
	--
	-- * The left argument's indices are lower than the right argument's indices
	, (<|), (|<), (>|), (|>)
	, (<>|), (|<>)
	-- * Query
	, null, size, member, notMember
	-- * Deletion
	, delete, filter, (\\)
	-- * Indexing
	, Index, findIndex, elemAt
	-- * List conversions
	, fromList, toAscList
	) where

import Control.Monad (guard)
import Data.Foldable (Foldable, foldl', foldMap, foldr, toList)
import Data.Function (on)
import Data.Map (Map)
import Data.Map.Util (Index, Tag, maxTag, minTag, nextHigherTag, nextLowerTag, readsPrecList, showsPrecList)
import Data.Set (Set) -- so the haddocks link to the right place
import Prelude hiding (filter, foldr, lookup, null)
import qualified Data.Map as M

data OSet a = OSet !(Map a Tag) !(Map Tag a)

-- | Values appear in insertion order, not ascending order.
instance Ord a => Semigroup (OSet a) where (<>) = foldl' (|>)
instance Ord a => Monoid (OSet a) where mempty = empty
instance Foldable OSet where foldMap f (OSet _ vs) = foldMap f vs
instance         Eq   a  => Eq   (OSet a) where (==)    = (==)    `on` toList
instance         Ord  a  => Ord  (OSet a) where compare = compare `on` toList
instance         Show a  => Show (OSet a) where showsPrec = showsPrecList toList
instance (Ord a, Read a) => Read (OSet a) where readsPrec = readsPrecList fromList

infixr 5 <|, |<   -- copy :
infixl 5 >|, |>
infixr 6 <>|, |<> -- copy <>

(<|) , (|<)  :: Ord a =>      a -> OSet a -> OSet a
(>|) , (|>)  :: Ord a => OSet a ->      a -> OSet a
(<>|), (|<>) :: Ord a => OSet a -> OSet a -> OSet a

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
(\\) :: Ord a => OSet a -> OSet a -> OSet a
o@(OSet ts vs) \\ o'@(OSet ts' vs') = if size o < size o'
	then filter (`notMember` o') o
	else foldr delete o vs'

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
