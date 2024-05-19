{-# LANGUAGE TupleSections #-}

-- | An 'OMap' behaves much like a 'M.Map', with mostly the same asymptotics, but
-- also remembers the order that keys were inserted. All operations whose
-- asymptotics are worse than 'M.Map' have documentation saying so.
module Data.Map.Ordered.Strict
	( OMap
	-- * Trivial maps
	, empty, singleton
	-- * Insertion
	-- | Conventions:
	--
	-- * The open side of an angle bracket points to an 'OMap'
	--
	-- * The pipe appears on the side whose indices take precedence if both sides contain the same key
	--
	-- * The left argument's indices are lower than the right argument's indices
	--
	-- * If both sides contain the same key, the tuple's value wins
	, (<|), (|<), (>|), (|>)
	, (<>|), (|<>), unionWithL, unionWithR
	, Bias(Bias, unbiased), L, R
	-- * Deletion
	, delete, filter, (\\)
	, (|/\), (/\|), intersectionWith
	-- * Query
	, null, size, member, notMember, lookup
	-- * Indexing
	, Index, findIndex, elemAt
	-- * List conversions
	, fromList, assocs, toAscList
	-- * 'M.Map' conversion
	, toMap
	) where

import Data.Foldable (foldl')
import qualified Data.Map.Strict as M
import Data.Map.Ordered.Internal
	( OMap(..), empty, (<>|), (|<>), delete, filter, (\\), (|/\), (/\|), null, size
	, member, notMember, lookup, findIndex, elemAt, assocs, toAscList, fromTV, toMap )
import Data.Map.Util
import Prelude hiding (filter, lookup, null)

infixr 5 <|, |< -- copy :
infixl 5 >|, |>

(<|) , (|<) :: Ord k => (,)  k v -> OMap k v -> OMap k v
(>|) , (|>) :: Ord k => OMap k v -> (,)  k v -> OMap k v

(k, v) <| OMap tvs kvs = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
	t = maybe (nextLowerTag kvs) fst (M.lookup k tvs)

(k, v) |< o = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
	t = nextLowerTag kvs
	OMap tvs kvs = delete k o

o >| (k, v) = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
	t = nextHigherTag kvs
	OMap tvs kvs = delete k o

OMap tvs kvs |> (k, v) = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
	t = maybe (nextHigherTag kvs) fst (M.lookup k tvs)

-- | Take the union. The first 'OMap' \'s argument's indices are lower than the
-- second. If a key appears in both maps, the first argument's index takes
-- precedence, and the supplied function is used to combine the values.
--
-- /O(r*log(r))/ where /r/ is the size of the result
--
-- @since 0.2
unionWithL :: Ord k => (k -> v -> v -> v) -> OMap k v -> OMap k v -> OMap k v
unionWithL = unionWithInternal (\t t' -> t )

-- | Take the union. The first 'OMap' \'s argument's indices are lower than the
-- second. If a key appears in both maps, the second argument's index takes
-- precedence, and the supplied function is used to combine the values.
--
-- /O(r*log(r))/ where /r/ is the size of the result
--
-- @since 0.2
unionWithR :: Ord k => (k -> v -> v -> v) -> OMap k v -> OMap k v -> OMap k v
unionWithR = unionWithInternal (\t t' -> t')

unionWithInternal :: Ord k => (Tag -> Tag -> Tag) -> (k -> v -> v -> v) -> OMap k v -> OMap k v -> OMap k v
unionWithInternal fT fKV (OMap tvs kvs) (OMap tvs' kvs') = fromTV tvs'' where
	bump  = case maxTag kvs  of
		Nothing -> 0
		Just k  -> -k-1
	bump' = case minTag kvs' of
		Nothing -> 0
		Just k  -> -k
	tvs'' = M.unionWithKey (\k (t,v) (t',v') -> (fT t t', fKV k v v'))
		(fmap (\(t,v) -> (bump +t,v)) tvs )
		(fmap (\(t,v) -> (bump'+t,v)) tvs')

singleton :: (k, v) -> OMap k v
singleton kv@(k, v) = OMap (M.singleton k (0, v)) (M.singleton 0 kv)

-- | If a key appears multiple times, the first occurrence is used for ordering
-- and the last occurrence is used for its value. The library author welcomes
-- comments on whether this default is sane.
fromList :: Ord k => [(k, v)] -> OMap k v
fromList = foldl' (|>) empty

-- | Take the intersection. The first 'OMap' \'s argument's indices are used for
-- the result.
--
-- /O(m*log(n\/(m+1)) + r*log(r))/ where /m/ is the size of the smaller map, /n/
-- is the size of the larger map, and /r/ is the size of the result.
--
-- @since 0.2
intersectionWith ::
	Ord k =>
	(k -> v -> v' -> v'') ->
	OMap k v -> OMap k v' -> OMap k v''
intersectionWith f (OMap tvs kvs) (OMap tvs' kvs') = fromTV
	$ M.intersectionWithKey (\k (t,v) (t',v') -> (t, f k v v')) tvs tvs'

-- | Alter the value (or its absence) associated with a key.
--
-- @since 0.2.4
alter :: Ord k => (Maybe v -> Maybe v) -> k -> OMap k v -> OMap k v
alter f k om@(OMap tvs kvs) = case M.lookup k tvs of
	Just (t, _) -> OMap
		(M.alter (fmap (t,) . f . fmap snd) k tvs)
		(M.alter (fmap (k,) . f . fmap snd) t kvs)
	Nothing -> maybe om ((om |>) . (k, )) $ f Nothing
