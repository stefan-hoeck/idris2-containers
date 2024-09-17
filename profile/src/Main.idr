module Main

import Data.List
import Data.Map as M
import Data.SortedMap as SM
import Profile

%default total

createList : Nat -> List (Nat,Nat)
createList n = map (\x => (x,plus x 1)) [0..n]

createMap : Nat -> Map Nat Nat
createMap n = M.fromList $ map (\x => (x,plus x 1)) [0..n]

createSortedMap : Nat -> SortedMap Nat Nat
createSortedMap n = SM.fromList $ map (\x => (x,plus x 1)) [0..n]

insertMap : Nat -> Map Nat Nat
insertMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = M.insert 0 2 m
  let m = M.insert 1 3 m
  let m = M.insert 2 4 m
  let m = M.insert 3 5 m
  let m = M.insert 4 6 m
  let m = M.insert 5 7 m
  let m = M.insert 6 8 m
  let m = M.insert 7 9 m
  let m = M.insert 8 10 m
  M.insert 9 11 m

insertSortedMap : Nat -> SortedMap Nat Nat
insertSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = SM.insert 0 2 m
  let m = SM.insert 1 3 m
  let m = SM.insert 2 4 m
  let m = SM.insert 3 5 m
  let m = SM.insert 4 6 m
  let m = SM.insert 5 7 m
  let m = SM.insert 6 8 m
  let m = SM.insert 7 9 m
  let m = SM.insert 8 10 m
  SM.insert 9 11 m

deleteMap : Nat -> Map Nat Nat
deleteMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = M.delete 9 m
  let m = M.delete 8 m
  let m = M.delete 7 m
  let m = M.delete 6 m
  let m = M.delete 5 m
  let m = M.delete 4 m
  let m = M.delete 3 m
  let m = M.delete 2 m
  let m = M.delete 1 m
  M.delete 0 m

deleteSortedMap : Nat -> SortedMap Nat Nat
deleteSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = SM.delete 9 m
  let m = SM.delete 8 m
  let m = SM.delete 7 m
  let m = SM.delete 6 m
  let m = SM.delete 5 m
  let m = SM.delete 4 m
  let m = SM.delete 3 m
  let m = SM.delete 2 m
  let m = SM.delete 1 m
  SM.delete 0 m

updateMap : Nat -> Map Nat Nat
updateMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = M.update f 0 m
  let m = M.update f 1 m
  let m = M.update f 2 m
  let m = M.update f 3 m
  let m = M.update f 4 m
  let m = M.update f 5 m
  let m = M.update f 6 m
  let m = M.update f 7 m
  let m = M.update f 8 m
  M.update f 9 m
  where
    f : (Nat -> Maybe Nat)
    f x = case x `mod` 2  == 0 of
            True  =>
              Nothing
            False =>
              Just $ x * x

updateSortedMap : Nat -> SortedMap Nat Nat
updateSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  let m = SM.update f 0 m
  let m = SM.update f 1 m
  let m = SM.update f 2 m
  let m = SM.update f 3 m
  let m = SM.update f 4 m
  let m = SM.update f 5 m
  let m = SM.update f 6 m
  let m = SM.update f 7 m
  let m = SM.update f 8 m
  SM.update f 9 m
  where
    f : (Maybe Nat -> Maybe Nat)
    f Nothing  = Nothing
    f (Just x) =
      case x `mod` 2  == 0 of
        True  =>
          Nothing
        False =>
          Just $ x * x

lookupMap : Nat -> Map Nat Nat
lookupMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  let v = M.lookup 0 m
  let v = M.lookup 1 m
  let v = M.lookup 2 m
  let v = M.lookup 3 m
  let v = M.lookup 4 m
  let v = M.lookup 5 m
  let v = M.lookup 6 m
  let v = M.lookup 0 m
  let v = M.lookup 8 m
  let v = M.lookup 9 m
  m

lookupSortedMap : Nat -> SortedMap Nat Nat
lookupSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  let v = SM.lookup 0 m
  let v = SM.lookup 1 m
  let v = SM.lookup 2 m
  let v = SM.lookup 3 m
  let v = SM.lookup 4 m
  let v = SM.lookup 5 m
  let v = SM.lookup 6 m
  let v = SM.lookup 0 m
  let v = SM.lookup 8 m
  let v = SM.lookup 9 m
  m

keysMap : Nat -> List Nat
keysMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  M.keys m

keysSortedMap : Nat -> List Nat
keysSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  SM.keys m

valuesMap : Nat -> List Nat
valuesMap n = do
  let m = M.fromList $ map (\x => (x,plus x 1)) [0..n]
  M.values m

valuesSortedMap : Nat -> List Nat
valuesSortedMap n = do
  let m = SM.fromList $ map (\x => (x,plus x 1)) [0..n]
  SM.values m

bench : Benchmark Void
bench = Group "map"
  [ Group "List"
     [ Single "1"       (basic createList 0)
     , Single "100"     (basic createList 99)
     , Single "1000"    (basic createList 999)
     ]
  , Group "fromListMap"
      [ Single "1"       (basic createMap 0)
      , Single "100"     (basic createMap 99)
      , Single "1000"    (basic createMap 999)
      ]
  , Group "fromListSortedMap"
      [ Single "1"      (basic createSortedMap 0)
      , Single "100"    (basic createSortedMap 99)
      , Single "1000"   (basic createSortedMap 999)
      ]
  , Group "insertMap"
      [ Single "10"      (basic insertMap 0)
      ]
  , Group "insertSortedMap"
      [ Single "10"      (basic insertSortedMap 0)
      ]
  , Group "deleteMap"
      [ Single "10"      (basic deleteMap 9)
      ]
  , Group "deleteSortedMap"
      [ Single "10"      (basic deleteSortedMap 9)
      ]
  , Group "updateMap"
      [ Single "10"      (basic updateMap 9)
      ]
  , Group "updateSortedMap"
      [ Single "10"      (basic updateSortedMap 9)
      ]
  , Group "lookupMap"
      [ Single "10"      (basic lookupMap 9)
      ]
  , Group "lookupSortedMap"
      [ Single "10"      (basic lookupSortedMap 9)
      ]
  , Group "keysMap"
      [ Single "1000000" (basic keysMap 999999)
      ]
  , Group "keysSortedMap"
      [ Single "1000000" (basic keysSortedMap 999999)
      ]
  , Group "valuesMap"
      [ Single "1000000" (basic valuesMap 999999)
      ]
  , Group "valuesSortedMap"
      [ Single "1000000" (basic valuesSortedMap 999999)
      ]
  ]

main : IO ()
main = do
  runDefault (const True) Details show bench
