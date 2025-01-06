module Data.BoundedQueue

import Data.SnocList
import Derive.Prelude

%language ElabReflection

%default total

||| An immutable structure which keeps
||| track of its size, with amortized O(1) dequeue operations.
export
record Front a where
  constructor F
  front  : List a
  flimit : Nat
  fsize  : Nat

%runElab derive "Front" [Show,Eq]

||| An immutable structure which keeps
||| track of its size, with amortized O(1) enqueue operations.
export
record Back a where
  constructor B
  back   : SnocList a
  blimit : Nat
  bsize  : Nat

%runElab derive "Back" [Show,Eq]

||| An immutable, bounded first-in first-out structure which keeps
||| track of its size, with amortized O(1) enqueue and dequeue operations.
||| The totalsize field keeps track of the combined sizes of the front and back.
export
record BoundedQueue a where
  constructor Q
  front     : Front a
  back      : Back a
  totalsize : Nat

||| The empty `BoundedQueue`. O(1)
export %inline
empty : Nat -> BoundedQueue a
empty l =
  Q (F [] 0 0)
    (B [<] l 0)
    0

||| Naively keeps the first `n` values of a list, and converts
||| into a `BoundedQueue` (keeps the order of the elements). O(1)
export %inline
fromList : Nat -> List a -> BoundedQueue a
fromList n vs =
  Q (F (take n vs) n (length $ take n vs))
    (B [<] 0 0)
    n

||| Naively keeps the first `n` values of a `SnocList`, and converts
||| into a `BoundedQueue` (keeps the order of the elements). O(1)
export %inline
fromSnocList : Nat -> SnocList a -> BoundedQueue a
fromSnocList n sv =
  Q (F [] 0 0)
    (B (cast $ take n $ toList sv) n (length $ take n $ toList sv))
    n

||| Converts a `BoundedQueue` to a `SnocList`, keeping the order
||| of elements. O(n)
export %inline
toSnocList : BoundedQueue a -> SnocList a
toSnocList (Q (F front _ _) (B back _ _) _) =
  back <>< front

||| Append a value at the back of the `BoundedQueue`. O(1)
export
enqueue : BoundedQueue a -> a -> BoundedQueue a
enqueue (Q (F front@(f::fs) flimit fsize) (B back blimit bsize) totalsize) v =
  case blimit == bsize of
    True  =>
      Q (F fs (flimit `minus` 1) (fsize `minus` 1))
        (B (back :< v) (blimit `plus` 1) (bsize `plus` 1))
        totalsize
    False =>
      case (fsize `plus` bsize) == totalsize of
        True  =>
          Q (F fs (flimit `minus` 1) (fsize `minus` 1))
            (B (back :< v) blimit (bsize `plus` 1))
            totalsize
        False =>
          Q (F front flimit fsize)
            (B (back :< v) blimit (bsize `plus` 1))
            totalsize
enqueue (Q (F [] flimit fsize) (B back blimit bsize)            totalsize) v =
  case blimit == bsize of
    True  =>
      case toList back of
        (h::t) =>
          Q (F t (bsize `minus` 1) (bsize `minus` 1))
            (B (Lin :< v) 1 1)
            totalsize
        []     =>
          assert_total $ idris_crash "Data.BoundedQueue.enqueue: impossible state"
    False =>
      case (fsize `plus` bsize) == totalsize of
        True  =>
          assert_total $ idris_crash "Data.BoundedQueue.enqueue: impossible state"
        False =>
          Q (F [] flimit fsize)
            (B (back :< v) blimit (bsize `plus` 1))
            totalsize

||| Take a value from the front of the queue.
|||
||| In case of the front being empty, this transfers
||| the back to the front, which runs in O(n). However,
||| every element in the queue is thus shifted at most
||| once before being dequeued, so this runs in amortized
||| O(1).
export
dequeue : BoundedQueue a -> Maybe (a, BoundedQueue a)
dequeue (Q (F front flimit fsize) (B back blimit bsize) totalsize) =
  case front of
    h::t =>
      Just (h, Q (F t flimit (fsize `minus` 1))
                 (B back blimit bsize)
                 (totalsize `minus` 1)
           )
    []   =>
      case back <>> [] of
        h::t =>
          Just (h, Q (F t (length t) (length t))
                     (B [<] 0 0)
                     (totalsize `minus` 1)
               )
        []   =>
          Nothing

||| We can prepend an element to our `Queue`, making it the new
||| "oldest" element. O(1)
|||
||| This is against the typical use case for a FIFO data
||| structure, but it allows us to conveniently implement
||| `peekOldest`.
export
prepend : a -> BoundedQueue a -> BoundedQueue a
prepend x (Q (F front@(f::fs) flimit fsize) (B back blimit bsize) totalsize) =
  case flimit == fsize of
    True  =>
      Q (F (x::fs) flimit fsize)
        (B back blimit bsize)
        totalsize
    False =>
      assert_total $ idris_crash "Data.BoundedQueue.prepend: impossible state"
prepend x (Q (F []            _      fsize) (B back blimit bsize) totalsize) =
  case blimit == bsize of
    True  =>
      case toList back of
        h::t =>
          Q (F [x] 1 1)
            (B (cast t) blimit (bsize `minus` 1))
            totalsize
        []   =>
          Q (F [x] 1 1)
            (B Lin 0 0)
            1
    False =>
      case (fsize `plus` bsize) == totalsize of
        True  =>
          assert_total $ idris_crash "Data.BoundedQueue.prepend: impossible state"
        False =>
          Q (F [x] 1 1)
            (B back blimit bsize)
            totalsize

||| Return the last element of the queue, plus the unmodified
||| queue.
|||
||| Note: `peekOldest` might involve a rearrangement of the elements
|||       just like `dequeue`. In order to keep our amortized O(1)
|||       runtime behavior, the newly arranged queue should be used
|||       henceforth.
export
peekOldest : BoundedQueue a -> Maybe (a, BoundedQueue a)
peekOldest q =
  case dequeue q of
    Just (v,Q (F front flimit fsize) (B back blimit bsize) totalsize) =>
      Just (v, Q (F (v::front) flimit fsize) (B back blimit bsize) (totalsize `plus` 1))
    Nothing                                                 =>
      Nothing

||| Appends two `BoundedQueues`. O(m + n)
export
(++) : BoundedQueue a -> BoundedQueue a -> BoundedQueue a
(Q (F front1 flimit1 fsize1) (B back1 blimit1 bsize1) totalsize1) ++ (Q (F front2 flimit2 fsize2) (B back2 blimit2 bsize2) totalsize2) =
  Q (F (front1 ++ (back1 <>> front2))
       ((length front1 `plus` length back1) `plus` length front2)
       ((length front1 `plus` length back1) `plus` length front2)
    )
    (B back2 blimit2 bsize2)
    (totalsize1 `plus` totalsize2)

||| Returns the length of the `BoundedQueue`. O(1).
export
length : BoundedQueue a -> Nat
length (Q (F _ _ fsize) (B _ _ bsize) totalsize) =
  totalsize

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

%runElab derive "BoundedQueue" [Show,Eq]

export %inline
Semigroup (BoundedQueue a) where
  (<+>) = (++)

export %inline
Monoid (BoundedQueue a) where
  neutral = empty 0

export
Functor BoundedQueue where
  map f (Q (F front flimit fsize) (B back blimit bsize) totalsize) =
    Q (F (map f front) flimit fsize)
      (B (map f back) blimit bsize)
      totalsize

export
Foldable BoundedQueue where
  toList (Q (F front _ _) (B back _ _) _) = back <>> front
  foldr f acc = foldr f acc . toSnocList
  foldl f acc = foldl f acc . toList
  foldMap f = foldMap f . toList
  foldlM f acc = foldlM f acc . toList
  null (Q (F front _ _) (B back _ _) _) = null front || null back
