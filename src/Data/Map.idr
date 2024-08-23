module Data.Map

import Data.Map.Internal

import Control.Monad.Identity
import Data.List
import Data.String
import Derive.Prelude

%hide Prelude.null

%default total

--------------------------------------------------------------------------------
--          Creating Maps
--------------------------------------------------------------------------------

||| The empty map. (O)1
public export
empty : Map k a
empty = Tip

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

public export
insert : Eq (Map k v) => Eq v => Ord k => k -> v -> Map k v -> Map k v
insert kx0 vx0 m = go kx0 kx0 vx0 m
  where
    go : k -> k -> v -> Map k v -> Map k v
    go orig _  x Tip                 = singleton orig x
    go orig kx x t@(Bin sz ky y l r) =
      case compare kx ky of
        LT =>
          case (go orig kx x l) == l of
            True  =>
              t
            False =>
              balanceL ky y (go orig kx x l) r
        GT =>
          case (go orig kx x r) == r of
            True  =>
              t
            False =>
              balanceR ky y l (go orig kx x r)
        EQ =>
          case (x == y && orig == ky) of
            True  =>
              t
            False =>
              Bin sz orig x l r

insertR : Eq (Map k v) => Eq v => Ord k => k -> v -> Map k v -> Map k v
insertR kx0 = go kx0 kx0
  where
    go : k -> k -> v -> Map k v -> Map k v
    go orig _  x Tip                = singleton orig x
    go orig kx x t@(Bin _ ky y l r) =
      case compare kx ky of
        LT =>
          case (go orig kx x l) == l of
            True  =>
              t
            False =>
              balanceL ky y (go orig kx x l) r
        GT =>
          case (go orig kx x r) == r of
            True  =>
              t
            False =>
              balanceR ky y l (go orig kx x r)
        EQ =>
          t

public export
insertWith : Ord k => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWith = go
  where
    go : (a -> a -> a) -> k -> a -> Map k a -> Map k a
    go _ kx x Tip               = singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT =>
          balanceL ky y (go f kx x l) r
        GT =>
          balanceR ky y l (go f kx x r)
        EQ =>
          Bin sy kx (f x y) l r

public export
insertWithKey : Ord k => (k -> v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWithKey = go
  where
    go : (k -> v -> v -> v) -> k -> v -> Map k v -> Map k v
    go _ kx x Tip               = singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT => balanceL ky y (go f kx x l) r
        GT => balanceR ky y l (go f kx x r)
        EQ => Bin sy kx (f kx x y) l r

public export
insertLookupWithKey : Ord k => (k -> v -> v -> v) -> k -> v -> Map k v -> (Maybe v,Map k v)
insertLookupWithKey f0 k0 x0 = go f0 k0 x0
  where
    go : (k -> a -> a -> a) -> k -> a -> Map k a -> (Maybe a,Map k a)
    go _ kx x Tip               = (Nothing,singleton kx x)
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT => let (found,l') = go f kx x l
                  t'         = balanceL ky y l' r
                in (found,t')
        GT => let (found,r') = go f kx x r
                  t'         = balanceR ky y l r'
                in (found,t')
        EQ => (Just y,Bin sy kx (f kx x y) l r)

--------------------------------------------------------------------------------
--          Deletion/Update
--------------------------------------------------------------------------------

public export
delete : Eq (Map k v) => Eq k => Ord k => k -> Map k v -> Map k v
delete = go
  where
    go : k -> Map k v -> Map k v
    go _ Tip                = Tip
    go k t@(Bin _ kx x l r) =
      case compare k kx of
        LT =>
          case (go k l) == l of
            True  =>
              t
            False =>
              balanceR kx x (go k l) r
        GT =>
          case (go k r) == r of
            True  =>
              t
            False =>
              balanceL kx x l (go k r)
        EQ =>
          glue l r

public export
adjustWithKey : Ord k => (k -> v -> v) -> k -> Map k v -> Map k v
adjustWithKey = go
  where
    go : (k -> v -> v) -> k -> Map k v -> Map k v
    go _ _ Tip               = Tip
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          Bin sx kx x (go f k l) r
        GT =>
          Bin sx kx x l (go f k r)
        EQ =>
          Bin sx kx (f kx x) l r

public export
adjust : Ord k => (v -> v) -> k -> Map k v -> Map k v
adjust f = adjustWithKey (\_, x => f x)

public export
updateWithKey : Ord k => (k -> v -> Maybe v) -> k -> Map k v -> Map k v
updateWithKey = go
  where
    go : (k -> v -> Maybe v) -> k -> Map k v -> Map k v
    go _ _ Tip               = Tip
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          balanceR kx x (go f k l) r
        GT =>
          balanceL kx x l (go f k r)
        EQ =>
          case f kx x of
            Just x' =>
              Bin sx kx x' l r
            Nothing =>
              glue l r

public export
update : Ord k => (v -> Maybe v) -> k -> Map k v -> Map k v
update f = updateWithKey (\_, x => f x)

public export
updateLookupWithKey : Ord k => (k -> v -> Maybe v) -> k -> Map k v -> (Maybe v,Map k v)
updateLookupWithKey f0 k0 = go f0 k0
 where
   go : (k -> v -> Maybe v) -> k -> Map k v -> (Maybe v,Map k v)
   go _ _ Tip               = (Nothing,Tip)
   go f k (Bin sx kx x l r) =
     case compare k kx of
       LT =>
         let (found,l') = go f k l
             t'         = balanceR kx x l' r
           in (found,t')
       GT =>
         let (found,r') = go f k r
             t'         = balanceL kx x l r'
           in (found,t')
       EQ =>
         case f kx x of
           Just x' =>
             (Just x',Bin sx kx x' l r)
           Nothing =>
             let glued = glue l r
               in (Just x,glued)

public export
alter : Ord k => (Maybe v -> Maybe v) -> k -> Map k v -> Map k v
alter = go
  where
    go : (Maybe v -> Maybe v) -> k -> Map k v -> Map k v
    go f k Tip               =
      case f Nothing of
        Nothing => Tip
        Just x  => singleton k x
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          balance kx x (go f k l) r
        GT =>
          balance kx x l (go f k r)
        EQ =>
          case f (Just x) of
            Just x' => Bin sx kx x' l r
            Nothing => glue l r

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

public export
lookup : Ord k => k -> Map k v -> Maybe v
lookup = go
  where
    go : k -> Map k v -> Maybe v
    go _ Tip              =
      Nothing
    go k (Bin _ kx x l r) =
      case compare k kx of
        LT => go k l
        GT => go k r
        EQ => Just x

public export
(!?) : Ord k => Map k v -> k -> Maybe v
(!?) m k = lookup k m

public export
member : Ord k => k -> Map k v -> Bool
member _ Tip              = False
member k (Bin _ kx _ l r) =
  case compare k kx of
    LT => member k l
    GT => member k r
    EQ => True

public export
notMember : Ord k => k -> Map k v -> Bool
notMember k m = not $ member k m

public export
find : Ord k => k -> Map k v -> v
find _ Tip              = assert_total $ idris_crash "Map.!: given key is not an element in the map"
find k (Bin _ kx x l r) =
  case compare k kx of
    LT => find k l
    GT => find k r
    EQ => x

public export
(!!) : Ord k => Map k v -> k -> v
(!!) m k = find k m

public export
findWithDefault : Ord k => v -> k -> Map k v -> v
findWithDefault def _ Tip              = def
findWithDefault def k (Bin _ kx x l r) =
  case compare k kx of
    LT => findWithDefault def k l
    GT => findWithDefault def k r
    EQ => x

public export
lookupLT : Ord k => k -> Map k v -> Maybe (k,v)
lookupLT = goNothing
  where
    goJust : k -> k -> v -> Map k v -> Maybe (k,v)
    goJust _ kx' x' Tip              = Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case k <= kx of
        True  => goJust k kx' x' l
        False => goJust k kx x r
    goNothing : k -> Map k v -> Maybe (k,v)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case k <= kx of
        True  => goNothing k l
        False => goJust k kx x r

public export
lookupGT : Ord k => k -> Map k v -> Maybe (k,v)
lookupGT = goNothing
  where
    goJust : k -> k -> v -> Map k v -> Maybe (k,v)
    goJust _ kx' x' Tip              = Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case k < kx of
        True  => goJust k kx x l 
        False => goJust k kx' x' r
    goNothing : k -> Map k v -> Maybe (k,v)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case k < kx of
        True  => goJust k kx x l
        False => goNothing k r

public export
lookupLE : Ord k => k -> Map k v -> Maybe (k,v)
lookupLE = goNothing
  where
    goJust : k -> k -> v -> Map k v -> Maybe (k,v)
    goJust _ kx' x' Tip              = Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case compare k kx of
        LT => goJust k kx' x' l
        EQ => Just (kx,x)
        GT => goJust k kx x r
    goNothing : k -> Map k v -> Maybe (k,v)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case compare k kx of
        LT => goNothing k l
        EQ => Just (kx,x)
        GT => goJust k kx x r

public export
lookupGE : Ord k => k -> Map k v -> Maybe (k,v)
lookupGE = goNothing
  where
    goJust : k -> k -> v -> Map k v -> Maybe (k,v)
    goJust _ kx' x' Tip              = Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case compare k kx of
        LT => goJust k kx x l
        EQ => Just (kx,x)
        GT => goJust k kx' x' r
    goNothing : k -> Map k v -> Maybe (k,v)
    goNothing _ Tip              = Nothing
    goNothing k (Bin _ kx x l r) =
      case compare k kx of
        LT => goJust k kx x l
        EQ => Just (kx,x)
        GT => goNothing k r

--------------------------------------------------------------------------------
--          Size
--------------------------------------------------------------------------------

public export
null : Map k v -> Bool
null Tip = True
null _   = False

--------------------------------------------------------------------------------
--          Filter
--------------------------------------------------------------------------------

splitMember : Ord k => k -> Map k v -> (Map k v,Bool,Map k v)
splitMember k0 m = go k0 m
  where
    go : k -> Map k v -> (Map k v,Bool,Map k v)
    go k t =
      case t of
        Tip            =>
          (Tip,False,Tip)
        Bin _ kx x l r =>
          case compare k kx of
            LT => let (lt,z,gt) = go k l
                    in (lt,z,link kx x gt r)
            GT => let (lt,z,gt) = go k r
                    in (link kx x l lt,z,gt)
            EQ => (l,True,r)

public export
splitRoot : Map k v -> List (Map k v)
splitRoot orig =
  case orig of
    Tip           =>
      []
    Bin _ k v l r =>
      [l,singleton k v,r]

public export
splitLookup : Ord k => k -> Map k v -> (Map k v,Maybe v,Map k v)
splitLookup k0 m = go k0 m
  where
    go : k -> Map k v -> (Map k v,Maybe v,Map k v)
    go k t =
      case t of
        Tip            =>
          (Tip,Nothing,Tip)
        Bin _ kx x l r =>
          case compare k kx of
          LT => let (lt,z,gt) = go k l
                  in (lt,z,link kx x gt r)
          GT => let (lt,z,gt) = go k r
                  in (link kx x l lt,z,gt)
          EQ => (l,Just x,r)

public export
split : Ord k => k -> Map k v -> (Map k v,Map k v)
split k0 t0 = go k0 t0
  where
    go : k -> Map k v -> (Map k v,Map k v)
    go k t =
      case t of
        Tip            =>
          (Tip,Tip)
        Bin _ kx x l r =>
          case compare k kx of
            LT => let (lt,gt) = go k l
                    in (lt,link kx x gt r)
            GT => let (lt,gt) = go k r
                    in (link kx x l lt,gt)
            EQ => (l,r)

public export
filterWithKey : Eq (Map k v) => (k -> v -> Bool) -> Map k v -> Map k v
filterWithKey _ Tip                = Tip
filterWithKey p t@(Bin _ kx x l r) =
  case p kx x of
    True  =>
      case (filterWithKey p l) == l && (filterWithKey p r) == r of
        True  =>
          t
        False =>
          link kx x (filterWithKey p l) (filterWithKey p r)
    False =>
      link2 (filterWithKey p l) (filterWithKey p r)

public export
filter : Eq (Map k v) => (v -> Bool) -> Map k v -> Map k v
filter p m = filterWithKey (\_, x => p x) m

public export
partitionWithKey : Eq (Map k v) => (k -> v -> Bool) -> Map k v -> (Map k v,Map k v)
partitionWithKey p0 t0 = go p0 t0
  where
    go : (k -> v -> Bool) -> Map k v -> (Map k v,Map k v)
    go _ Tip                = (Tip,Tip)
    go p t@(Bin _ kx x l r) =
      case p kx x of
        True  =>
          ( case (fst $ go p l) == l && (fst $ go p r) == r of
             True  =>
               t
             False =>
               link kx x (fst $ go p l) (fst $ go p r)
          , link2 (snd $ go p l) (snd $ go p r)
          )
        False =>
          ( link2 (fst $ go p l) (fst $ go p r)
          , case (snd $ go p l) == l && (snd $ go p r) == r of
              True  =>
                t
              False =>
                link kx x (snd $ go p l) (snd $ go p r)
          )

public export
takeWhileAntitone : (k -> Bool) -> Map k v -> Map k v
takeWhileAntitone _ Tip              = Tip
takeWhileAntitone p (Bin _ kx x l r) =
  case p kx of
    True  =>
      link kx x l (takeWhileAntitone p r)
    False =>
      takeWhileAntitone p l

public export
dropWhileAntitone : (k -> Bool) -> Map k v -> Map k v
dropWhileAntitone _ Tip              = Tip
dropWhileAntitone p (Bin _ kx x l r) =
  case p kx of
    True  =>
      dropWhileAntitone p r
    False =>
      link kx x (dropWhileAntitone p l) r

public export
spanAntitone : (k -> Bool) -> Map k v -> (Map k v, Map k v)
spanAntitone p0 m = go p0 m
  where
    go : (k -> Bool) -> Map k v -> (Map k v,Map k v)
    go _ Tip              = (Tip,Tip)
    go p (Bin _ kx x l r) =
      case p kx of
        True  =>
          let (u,v) = go p r
            in (link kx x l u,v)
        False =>
          let (u,v) = go p l
            in (u,link kx x v r)

public export
mapMaybeWithKey : (k -> a -> Maybe b) -> Map k a -> Map k b
mapMaybeWithKey _ Tip              = Tip
mapMaybeWithKey f (Bin _ kx x l r) =
  case f kx x of
    Just y  =>
      link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
    Nothing =>
      link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)

public export
mapMaybe : (a -> Maybe b) -> Map k a -> Map k b
mapMaybe f = mapMaybeWithKey (\_, x => f x)

public export
mapEitherWithKey : (k -> a -> Either b c) -> Map k a -> (Map k b, Map k c)
mapEitherWithKey f0 t0 = go f0 t0
  where
    go : (k -> a -> Either b c) -> Map k a -> (Map k b,Map k c)
    go _ Tip              = (Tip,Tip)
    go f (Bin _ kx x l r) =
      case f kx x of
        Left  y => (link kx y (fst $ go f l) (fst $ go f r),link2 (snd $ go f l) (snd $ go f r))
        Right z => (link2 (fst $ go f l) (fst $ go f r),link kx z (snd $ go f l) (snd $ go f r))

public export
mapEither : (a -> Either b c) -> Map k a -> (Map k b, Map k c)
mapEither f m = mapEitherWithKey (\_, x => f x) m

{-
--------------------------------------------------------------------------------
--          Combine
--------------------------------------------------------------------------------

union : Ord k => Map k v -> Map k v -> Map k v
union t1 Tip                 = t1
union t1 (Bin _ k x Tip Tip) = insert k x t1
union (Bin _ k x Tip Tip) t2 = insert k x t2
union Tip t2 = t2
union t1@(Bin _ k1 x1 l1 r1) t2 = case split k1 t2 of
  (l2, r2) | l1l2 `ptrEq` l1 && r1r2 `ptrEq` r1 -> t1
           | otherwise -> link k1 x1 l1l2 r1r2
           where !l1l2 = union l1 l2
                 !r1r2 = union r1 r2
-}

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

public export
foldl : (v -> w -> v) -> v -> Map k w -> v
foldl f z Tip             = z
foldl f z (Bin _ _ x l r) = foldl f (f (foldl f z l) x) r

public export
foldr : (v -> w -> w) -> w -> Map k v -> w
foldr f z Tip             = z 
foldr f z (Bin _ _ x l r) = foldr f (f x (foldr f z r)) l

public export
foldlWithKey : (v -> k -> w -> v) -> v -> Map k w -> v
foldlWithKey f z Tip              = z
foldlWithKey f z (Bin _ kx x l r) = foldlWithKey f (f (foldlWithKey f z l) kx x) r

public export
foldrWithKey : (k -> v -> w -> w) -> w -> Map k v -> w
foldrWithKey f z Tip              = z
foldrWithKey f z (Bin _ kx x l r) = foldrWithKey f (f kx x (foldrWithKey f z r)) l

--------------------------------------------------------------------------------
--          Traversal
--------------------------------------------------------------------------------

public export
map : (v -> w) -> Map k v -> Map k w
map _ Tip               = Tip
map f (Bin sx kx x l r) = Bin sx kx (f x) (map f l) (map f r)

public export
mapWithKey : (k -> v -> w) -> Map k v -> Map k w
mapWithKey _ Tip               = Tip
mapWithKey f (Bin sx kx x l r) = Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r)

public export
mapAccumL : (v -> k -> w -> (v,c)) -> v -> Map k w -> (v,Map k c)
mapAccumL _ a Tip               = (a,Tip)
mapAccumL f a (Bin sx kx x l r) =
  let (a1,l') = mapAccumL f a l
      (a2,x') = f a1 kx x
      (a3,r') = mapAccumL f a2 r
  in (a3,Bin sx kx x' l' r')

public export
mapAccumRWithKey : (v -> k -> w -> (v,c)) -> v -> Map k w -> (v,Map k c)
mapAccumRWithKey _ a Tip               = (a,Tip)
mapAccumRWithKey f a (Bin sx kx x l r) =
  let (a1,r') = mapAccumRWithKey f a r
      (a2,x') = f a1 kx x
      (a3,l') = mapAccumRWithKey f a2 l
  in (a3,Bin sx kx x' l' r')

public export
mapAccumWithKey : (v -> k -> w -> (v,c)) -> v -> Map k w -> (v,Map k c)
mapAccumWithKey f a t = mapAccumL f a t

public export
mapAccum : (v -> w -> (v,c)) -> v -> Map k w -> (v,Map k c)
mapAccum f a m = mapAccumWithKey (\a', _, x' => f a' x') a m

--------------------------------------------------------------------------------
--          Compose
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

public export
toDescList : Map k v -> List (k,v)
toDescList Tip               = []
toDescList t@(Bin _ _ _ _ _) = foldlWithKey (\xs, k, x => (k,x) :: xs) [] t

public export
toAscList : Map k v -> List (k,v)
toAscList Tip               = []
toAscList t@(Bin _ _ _ _ _) = foldrWithKey (\k, x, xs => (k,x) :: xs) [] t

||| Convert the map to a list of key/value pairs.
public export
toList : Map k v -> List (k,v)
toList = toAscList

--------------------------------------------------------------------------------
--          Keys
--------------------------------------------------------------------------------

||| Gets the keys of the map.
public export
keys : Map k v -> List k
keys = map fst . toList

--------------------------------------------------------------------------------
--          Values
--------------------------------------------------------------------------------

||| Gets the values of the map.
||| Could contain duplicates.
public export
values : Map k v -> List v
values = map snd . toList

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

public export
Functor (Map k) where
  map f m = map f m

public export
Foldable (Map k) where
  foldl f z = foldl f z . values 
  foldr f z = foldr f z . values 
  null      = null
