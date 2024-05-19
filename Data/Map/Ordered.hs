{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

-- | An 'OMap' behaves much like a 'M.Map', with mostly the same asymptotics, but
-- also remembers the order that keys were inserted. All operations whose
-- asymptotics are worse than 'M.Map' have documentation saying so.
module Data.Map.Ordered
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
	-- * Deletion/Update
	, delete, filter, (\\)
	, (|/\), (/\|), intersectionWith
	, alter
	-- * Query
	, null, size, member, notMember, lookup
	-- * Indexing
	, Index, findIndex, elemAt
	-- * List conversions
	, fromList, assocs, toAscList
	-- * 'M.Map' conversion
	, toMap
	) where

import qualified Data.Map as M
import Data.Map.Ordered.Internal
import Data.Map.Util
import Prelude hiding (filter, lookup, null)

singleton :: (k, v) -> OMap k v
singleton kv@(k, v) = OMap (M.singleton k (0, v)) (M.singleton 0 kv)

-- | Alter the value (or its absence) associated with a key.
--
-- @since 0.2.3
alter :: Ord k => (Maybe v -> Maybe v) -> k -> OMap k v -> OMap k v
alter f k om@(OMap tvs kvs) = case M.lookup k tvs of
	Just (t, _) -> OMap
		(M.alter (fmap (t,) . f . fmap snd) k tvs)
		(M.alter (fmap (k,) . f . fmap snd) t kvs)
	Nothing -> maybe om ((om |>) . (k, )) $ f Nothing
