{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Map.Ordered.Internal where

import Control.Monad (guard)
import Data.Data
import Data.Foldable (Foldable, foldl', foldMap)
import Data.Function (on)
import Data.Map (Map)
import Data.Map.Util
import Data.Monoid (Monoid(..))
#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup(..))
#endif
#if !(MIN_VERSION_base(4,8,0))
import Control.Applicative ((<$>))
import Data.Traversable
#endif
import Prelude hiding (filter, lookup, null)
import qualified Data.Map as M
import qualified GHC.Exts as Exts

data OMap k v = OMap !(Map k (Tag, v)) !(Map Tag (k, v))
	deriving (Functor, Typeable)

-- | Values are produced in insertion order, not key order.
instance Foldable (OMap k) where foldMap f (OMap _ kvs) = foldMap (f . snd) kvs
instance (       Eq   k, Eq   v) => Eq   (OMap k v) where (==)    = (==)    `on` assocs
instance (       Ord  k, Ord  v) => Ord  (OMap k v) where compare = compare `on` assocs
instance (       Show k, Show v) => Show (OMap k v) where showsPrec = showsPrecList assocs
instance (Ord k, Read k, Read v) => Read (OMap k v) where readsPrec = readsPrecList fromList

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.
instance (Data k, Data a, Ord k) => Data (OMap k a) where
	gfoldl f z m   = z fromList `f` assocs m
	toConstr _     = fromListConstr
	gunfold k z c  = case constrIndex c of
		1 -> k (z fromList)
		_ -> error "gunfold"
	dataTypeOf _   = oMapDataType
	-- dataCast2 /must/ be eta-expanded in order to build on GHC 7.8.
	dataCast2 f    = gcast2 f

fromListConstr :: Constr
fromListConstr = mkConstr oMapDataType "fromList" [] Prefix

oMapDataType :: DataType
oMapDataType = mkDataType "Data.Map.Ordered.Map" [fromListConstr]

-- | @'GHC.Exts.fromList' = 'fromList'@ and @'GHC.Exts.toList' = 'assocs'@.
-- @since 0.2.3
instance Ord k => Exts.IsList (OMap k v) where
	type Item (OMap k v) = (k, v)
	fromList = fromList
	toList = assocs

#if MIN_VERSION_base(4,9,0)
instance (Ord k, Semigroup v) => Semigroup (Bias L (OMap k v)) where
	Bias o <> Bias o' = Bias (unionWithL (const (<>)) o o')
instance (Ord k, Semigroup v) => Semigroup (Bias R (OMap k v)) where
	Bias o <> Bias o' = Bias (unionWithR (const (<>)) o o')
#endif

-- | Empty maps and map union. When combining two sets that share elements, the
-- indices of the left argument are preferred, and the values are combined with
-- 'mappend'.
--
-- See the asymptotics of 'unionWithL'.
instance (Ord k, Monoid v) => Monoid (Bias L (OMap k v)) where
	mempty = Bias empty
	mappend (Bias o) (Bias o') = Bias (unionWithL (const mappend) o o')

-- | Empty maps and map union. When combining two sets that share elements, the
-- indices of the right argument are preferred, and the values are combined
-- with 'mappend'.
--
-- See the asymptotics of 'unionWithR'.
instance (Ord k, Monoid v) => Monoid (Bias R (OMap k v)) where
	mempty = Bias empty
	mappend (Bias o) (Bias o') = Bias (unionWithR (const mappend) o o')

-- | Values are traversed in insertion order, not key order.
--
-- /O(n*log(n))/ where /n/ is the size of the map.
instance Ord k => Traversable (OMap k) where
	traverse f (OMap tvs kvs) = fromKV <$> traverse (\(k,v) -> (,) k <$> f v) kvs

infixr 5 <|, |< -- copy :
infixl 5 >|, |>
infixr 6 <>|, |<> -- copy <>

(<|) , (|<) :: Ord k => (,)  k v -> OMap k v -> OMap k v
(>|) , (|>) :: Ord k => OMap k v -> (,)  k v -> OMap k v

-- | When a key occurs in both maps, prefer the value from the second map.
--
-- See asymptotics of 'unionWithR'.
(<>|) :: Ord k => OMap k v -> OMap k v -> OMap k v

-- | When a key occurs in both maps, prefer the value from the first map.
--
-- See asymptotics of 'unionWithL'.
(|<>) :: Ord k => OMap k v -> OMap k v -> OMap k v

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

(<>|) = unionWithR (const const)
(|<>) = unionWithL (const const)

-- | Take the union. The first 'OMap' \'s argument's indices are lower than the
-- second. If a key appears in both maps, the first argument's index takes
-- precedence, and the supplied function is used to combine the values.
--
-- /O(r*log(r))/ where /r/ is the size of the result
unionWithL :: Ord k => (k -> v -> v -> v) -> OMap k v -> OMap k v -> OMap k v
unionWithL = unionWithInternal (\t t' -> t )

-- | Take the union. The first 'OMap' \'s argument's indices are lower than the
-- second. If a key appears in both maps, the second argument's index takes
-- precedence, and the supplied function is used to combine the values.
--
-- /O(r*log(r))/ where /r/ is the size of the result
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

-- | @m \\\\ n@ deletes all the keys that exist in @n@ from @m@
--
-- /O(m*log(n))/ where /m/ is the size of the smaller map and /n/ is the size
-- of the larger map.
(\\) :: Ord k => OMap k v -> OMap k v' -> OMap k v
o@(OMap tvs kvs) \\ o'@(OMap tvs' kvs') = if size o < size o'
	then filter (const . (`notMember` o')) o
	else foldr delete o (fmap fst (assocs o'))

empty :: OMap k v
empty = OMap M.empty M.empty

singleton :: (k, v) -> OMap k v
singleton kv@(k, v) = OMap (M.singleton k (0, v)) (M.singleton 0 kv)

-- | If a key appears multiple times, the first occurrence is used for ordering
-- and the last occurrence is used for its value. The library author welcomes
-- comments on whether this default is sane.
fromList :: Ord k => [(k, v)] -> OMap k v
fromList = foldl' (|>) empty

null :: OMap k v -> Bool
null (OMap tvs _) = M.null tvs

size :: OMap k v -> Int
size (OMap tvs _) = M.size tvs

member, notMember :: Ord k => k -> OMap k v -> Bool
member    k (OMap tvs _) = M.member    k tvs
notMember k (OMap tvs _) = M.notMember k tvs

lookup :: Ord k => k -> OMap k v -> Maybe v
lookup k (OMap tvs _) = fmap snd (M.lookup k tvs)

-- The Ord constraint is for compatibility with older (<0.5) versions of
-- containers.
-- | @filter f m@ contains exactly the key-value pairs of @m@ that satisfy @f@,
-- without changing the order they appear
filter :: Ord k => (k -> v -> Bool) -> OMap k v -> OMap k v
filter f (OMap tvs kvs) = OMap (M.filterWithKey (\k (t, v) -> f k v) tvs)
                               (M.filterWithKey (\t (k, v) -> f k v) kvs)

delete :: Ord k => k -> OMap k v -> OMap k v
delete k o@(OMap tvs kvs) = case M.lookup k tvs of
	Nothing     -> o
	Just (t, _) -> OMap (M.delete k tvs) (M.delete t kvs)

-- | Intersection. (The @/\\@ is intended to look a bit like the standard
-- mathematical notation for set intersection.)
--
-- See asymptotics of 'intersectionWith'.
(/\|) :: Ord k => OMap k v -> OMap k v' -> OMap k v
o /\| o' = intersectionWith (\k v' v -> v) o' o

-- | Intersection. (The @/\\@ is intended to look a bit like the standard
-- mathematical notation for set intersection.)
--
-- See asymptotics of 'intersectionWith'.
(|/\) :: Ord k => OMap k v -> OMap k v' -> OMap k v
o |/\ o' = intersectionWith (\k v v' -> v) o o'

-- | Take the intersection. The first 'OMap' \'s argument's indices are used for
-- the result.
--
-- /O(m*log(n\/(m+1)) + r*log(r))/ where /m/ is the size of the smaller map, /n/
-- is the size of the larger map, and /r/ is the size of the result.
intersectionWith ::
	Ord k =>
	(k -> v -> v' -> v'') ->
	OMap k v -> OMap k v' -> OMap k v''
intersectionWith f (OMap tvs kvs) (OMap tvs' kvs') = fromTV
	$ M.intersectionWithKey (\k (t,v) (t',v') -> (t, f k v v')) tvs tvs'

fromTV :: Ord k => Map k (Tag, v) -> OMap k v
fromTV tvs = OMap tvs kvs where
	kvs = M.fromList [(t,(k,v)) | (k,(t,v)) <- M.toList tvs]

fromKV :: Ord k => Map Tag (k, v) -> OMap k v
fromKV kvs = OMap tvs kvs where
	tvs = M.fromList [(k,(t,v)) | (t,(k,v)) <- M.toList kvs]

findIndex :: Ord k => k -> OMap k v -> Maybe Index
findIndex k o@(OMap tvs kvs) = do
	(t, _) <- M.lookup k tvs
	M.lookupIndex t kvs

elemAt :: OMap k v -> Index -> Maybe (k, v)
elemAt o@(OMap tvs kvs) i = do
	guard (0 <= i && i < M.size kvs)
	return . snd $ M.elemAt i kvs

-- | Return key-value pairs in the order they were inserted.
assocs :: OMap k v -> [(k, v)]
assocs (OMap _ kvs) = map snd $ M.toAscList kvs

-- | Return key-value pairs in order of increasing key.
toAscList :: OMap k v -> [(k, v)]
toAscList (OMap tvs kvs) = map (\(k, (t, v)) -> (k, v)) $ M.toAscList tvs

-- | Convert an 'OMap' to a 'Map'.
--
-- /O(n)/, where /n/ is the size of the 'OMap'.
toMap :: OMap k v -> Map k v
toMap (OMap tvs _) = fmap snd tvs

-- | Alter the value at k, or absence of. Can be used to insert delete or update
--   with the same semantics as 'Map's alter
alter :: Ord k => (Maybe v -> Maybe v) -> k -> OMap k v -> OMap k v
alter f k om@(OMap tvs kvs) =
  case fst <$> M.lookup k tvs of
    Just t -> OMap (M.alter (fmap (t,) . f . fmap snd) k tvs)
                   (M.alter (fmap (k,) . f . fmap snd) t kvs)
    Nothing -> maybe om ((om |>) . (k, )) $ f Nothing
