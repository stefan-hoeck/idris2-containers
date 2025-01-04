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
export
record BoundedQueue a where
  constructor Q
  front  : Front a
  back   : Back a

||| The empty `BoundedQueue`. O(1)
export %inline
empty : Nat -> BoundedQueue a
empty l =
  Q (F [] l 0)
    (B [<] l 0)

||| Naively keeps the first `n` values of a list, and converts
||| into a `BoundedQueue` (keeps the order of the elements). O(1)
export %inline
fromList : Nat -> List a -> BoundedQueue a
fromList n vs =
  Q (F (take n vs) n (length $ take n vs))
    (B [<] n 0)

||| Naively keeps the first `n` values of a `SnocList`, and converts
||| into a `BoundedQueue` (keeps the order of the elements). O(1)
export %inline
fromSnocList : Nat -> SnocList a -> BoundedQueue a
fromSnocList n sv =
  Q (F [] n 0)
    (B (cast $ take n $ toList sv) n (length $ take n $ toList sv))

||| Converts a `BoundedQueue` to a `SnocList`, keeping the order
||| of elements. O(n)
export %inline
toSnocList : BoundedQueue a -> SnocList a
toSnocList (Q (F front _ _) (B back _ _)) =
  back <>< front

||| Append a value at the back of the `BoundedQueue`. O(1)
export
enqueue : BoundedQueue a -> a -> BoundedQueue a
enqueue (Q (F front@(f::fs) flimit fsize) (B back blimit bsize)) v =
  case blimit == bsize of
    True  =>
      Q (F fs flimit fsize)
        (B (back :< v) blimit bsize)
    False =>
      Q (F front flimit fsize)
        (B (back :< v) blimit (bsize `plus` 1))
enqueue (Q (F [] flimit fsize) (B back blimit bsize))            v =
  Q (F [] flimit fsize)
    (B (back :< v) blimit bsize)

||| Take a value from the front of the queue.
|||
||| In case of the front being empty, this transfers
||| the back to the front, which runs in O(n). However,
||| every element in the queue is thus shifted at most
||| once before being dequeued, so this runs in amortized
||| O(1).
export
dequeue : BoundedQueue a -> Maybe (a, BoundedQueue a)
dequeue (Q (F front flimit fsize) (B back blimit bsize)) =
  case front of
    (h::t) => Just (h, Q (F t flimit (fsize `minus` 1))
                         (B back blimit bsize)
                   )
    []     =>
      case back <>> [] of
        h::t => Just (h, Q (F t flimit (length t)) (B [<] blimit 0))
        []   => Nothing

||| We can prepend an element to our `Queue`, making it the new
||| "oldest" element. O(1)
|||
||| This is against the typical use case for a FIFO data
||| structure, but it allows us to conveniently implement
||| `peekOldest`.
export
prepend : a -> BoundedQueue a -> BoundedQueue a
prepend x (Q (F front@(f::fs) flimit fsize) back) =
  case flimit == fsize of
    True  =>
      Q (F (x::fs) flimit fsize)
        back
    False =>
      Q (F (x::front) flimit (fsize `plus` 1))
        back
prepend x (Q (F []            flimit _)     back) =
  Q (F [x] flimit 1)
    back

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
    Just (v,Q (F front flimit fsize) (B back blimit bsize)) =>
      Just (v, Q (F (v::front) flimit fsize) (B back blimit bsize))
    Nothing                                                 =>
      Nothing

||| Appends two `BoundedQueues`. O(m + n)
export
(++) : BoundedQueue a -> BoundedQueue a -> BoundedQueue a
(Q (F front1 flimit1 fsize1) (B back1 blimit1 bsize1)) ++ (Q (F front2 flimit2 fsize2) (B back2 blimit2 bsize2)) =
  Q (F (front1 ++ (back1 <>> front2))
       ((length front1 `plus` length back1) `plus` length front2)
       ((length front1 `plus` length back1) `plus` length front2)
    )
    (B back2 blimit2 bsize2)

||| Returns the length of the `BoundedQueue`. O(1).
export
length : BoundedQueue a -> Nat
length (Q (F _ _ fsize) (B _ _ bsize)) =
  fsize `plus` bsize

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
  map f (Q (F front flimit fsize) (B back blimit bsize)) =
    Q (F (map f front) flimit fsize)
      (B (map f back) blimit bsize)

export
Foldable BoundedQueue where
  toList (Q (F front _ _) (B back _ _)) = back <>> front
  foldr f acc = foldr f acc . toSnocList
  foldl f acc = foldl f acc . toList
  foldMap f = foldMap f . toList
  foldlM f acc = foldlM f acc . toList
  null (Q (F front _ _) (B back _ _)) = null front || null back
