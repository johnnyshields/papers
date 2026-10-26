/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Finite ribbon census model

Computable ribbon coordinates and integer determinant census for “Composition
and reversal” (`rem:factorwise`) in “The seam chain and the composition problem”
(`sec:application`).  Literal tables are identified with the computed determinants
by kernel reduction before collision checking.  The geometric specialization
bridge is supplied by `FactorwiseCensus`.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators Matrix

/-- The outer boundary of the canonical ribbon, written without truncated suffix subtraction. -/
def ribbonOuter {n : ℕ} (w : Fin n → ℕ) (i : Fin n) : ℕ :=
  1 + ∑ k : Fin n, if i ≤ k then w k - 1 else 0

/-- The inner boundary of the canonical ribbon. -/
def ribbonInner {n : ℕ} (w : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∑ k : Fin n, if i < k then w k - 1 else 0

/-- A sparse Laplace expansion whose zero terms are not recursively expanded. -/
def censusDet : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, _ => 1
  | n + 1, M => ∑ j : Fin (n + 1), if M 0 j = 0 then 0 else
      (-1 : ℤ) ^ j.val * M 0 j * censusDet n (M.submatrix Fin.succ j.succAbove)

/-- Two integral specializations used only to distinguish the finitely many census entries. -/
def censusValues (t : Bool) : List ℤ :=
  if t then [31, 73, 127, 293, 541, 887, 1429, 2381, 3889]
  else [17, 43, 97, 179, 337, 613, 1091, 1907, 3253]

/-- The complete-generator convention after the integral specialization. -/
def censusComplete (t : Bool) (k : ℤ) : ℤ :=
  if k = 0 then 1 else if 0 < k then (censusValues t).getD (k.toNat - 1) 0 else 0

/-- A computable specialization of the canonical ribbon's actual Jacobi--Trudi matrix. -/
def censusMatrix (t : Bool) (a : List ℕ) : Matrix (Fin a.length) (Fin a.length) ℤ :=
  fun i j => censusComplete t
    ((ribbonOuter a.get i : ℤ) - ribbonInner a.get j - i.val + j.val)

/-- The finite signature is a pair of actual specialized determinants. -/
def ribbonCensusSignature (a : List ℕ) : ℤ × ℤ :=
  (censusDet a.length (censusMatrix false a), censusDet a.length (censusMatrix true a))

/-- A finite list enumerating compositions with at most `fuel` positive parts and total `N`. -/
def censusWords : ℕ → ℕ → List (List ℕ)
  | 0, N => if N = 0 then [[]] else []
  | fuel + 1, N => if N = 0 then [[]] else
      (List.range N).flatMap fun k =>
        (censusWords fuel (N - (k + 1))).map fun a => (k + 1) :: a

/-- The evaluated records retain the entire composition alongside its signature. -/
def censusRecords (N : ℕ) : List (List ℕ × (ℤ × ℤ)) :=
  (censusWords N N).map fun a => (a, ribbonCensusSignature a)

private def censusRecordsCached0 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([], (1, 1))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_0 :
    censusRecords 0 = censusRecordsCached0 := by
  decide

private def censusRecordsCached1 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([1], (17, 31))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_1 :
    censusRecords 1 = censusRecordsCached1 := by
  decide

private def censusRecordsCached2 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([1, 1], (246, 888)),
    ([2], (43, 73))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_2 :
    censusRecords 2 = censusRecordsCached2 := by
  decide

private def censusRecordsCached3 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([1, 1, 1], (3548, 25392)),
    ([1, 2], (634, 2136)),
    ([2, 1], (634, 2136)),
    ([3], (97, 127))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_3 :
    censusRecords 3 = censusRecordsCached3 := by
  decide

private def censusRecordsCached4 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([1, 1, 1, 1], (51208, 725972)),
    ([1, 1, 2], (9108, 61180)),
    ([1, 2, 1], (9308, 62572)),
    ([1, 3], (1470, 3644)),
    ([2, 1, 1], (9108, 61180)),
    ([2, 2], (1670, 5036)),
    ([3, 1], (1470, 3644)),
    ([4], (179, 293))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_4 :
    censusRecords 4 = censusRecordsCached4 := by
  decide

private def censusRecordsCached5 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([1, 1, 1, 1, 1], (739128, 20755750)),
    ([1, 1, 1, 2], (131408, 1749382)),
    ([1, 1, 2, 1], (133680, 1792346)),
    ([1, 1, 3], (21156, 104234)),
    ([1, 2, 1, 1], (133680, 1792346)),
    ([1, 2, 2], (24556, 147386)),
    ([1, 3, 1], (22284, 104422)),
    ([1, 4], (2706, 8542)),
    ([2, 1, 1, 1], (131408, 1749382)),
    ([2, 1, 2], (23428, 147198)),
    ([2, 2, 1], (24556, 147386)),
    ([2, 3], (3834, 8730)),
    ([3, 1, 1], (21156, 104234)),
    ([3, 2], (3834, 8730)),
    ([4, 1], (2706, 8542)),
    ([5], (337, 541))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_5 :
    censusRecords 5 = censusRecordsCached5 := by
  decide

private def censusRecordsCached6 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([1, 1, 1, 1, 1, 1], (10668470, 593412778)),
    ([1, 1, 1, 1, 2], (1896706, 50015472)),
    ([1, 1, 1, 2, 1], (1928698, 51250358)),
    ([1, 1, 1, 3], (305238, 2980484)),
    ([1, 1, 2, 1, 1], (1919834, 51340886)),
    ([1, 1, 2, 2], (352726, 4221840)),
    ([1, 1, 3, 1], (320734, 2986954)),
    ([1, 1, 4], (38918, 244300)),
    ([1, 2, 1, 1, 1], (1928698, 51250358)),
    ([1, 2, 1, 2], (343862, 4312368)),
    ([1, 2, 2, 1], (361070, 4313578)),
    ([1, 2, 3], (56382, 255388)),
    ([1, 3, 1, 1], (320734, 2986954)),
    ([1, 3, 2], (58094, 250128)),
    ([1, 4, 1], (40886, 248918)),
    ([1, 5], (5116, 15884)),
    ([2, 1, 1, 1, 1], (1896706, 50015472)),
    ([2, 1, 1, 2], (337230, 4215370)),
    ([2, 1, 2, 1], (343862, 4312368)),
    ([2, 1, 3], (54414, 250770)),
    ([2, 2, 1, 1], (352726, 4221840)),
    ([2, 2, 2], (64726, 347126)),
    ([2, 3, 1], (58094, 250128)),
    ([2, 4], (7084, 20502)),
    ([3, 1, 1, 1], (305238, 2980484)),
    ([3, 1, 2], (54414, 250770)),
    ([3, 2, 1], (56382, 255388)),
    ([3, 3], (8796, 15242)),
    ([4, 1, 1], (38918, 244300)),
    ([4, 2], (7084, 20502)),
    ([5, 1], (5116, 15884)),
    ([6], (613, 887))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_6 :
    censusRecords 6 = censusRecordsCached6 := by
  decide

private def censusRecordsCached7 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([1, 1, 1, 1, 1, 1, 1], (153987142, 16965839296)),
    ([1, 1, 1, 1, 1, 2], (27376848, 1429956822)),
    ([1, 1, 1, 1, 2, 1], (27838346, 1465266704)),
    ([1, 1, 1, 1, 3], (4405656, 85212928)),
    ([1, 1, 1, 2, 1, 1], (27698842, 1468041728)),
    ([1, 1, 1, 2, 2], (5089024, 120719370)),
    ([1, 1, 1, 3, 1], (4627526, 85409488)),
    ([1, 1, 1, 4], (561520, 6985516)),
    ([1, 1, 2, 1, 1, 1], (27698842, 1468041728)),
    ([1, 1, 2, 1, 2], (4938336, 123525738)),
    ([1, 1, 2, 2, 1], (5186438, 123561520)),
    ([1, 1, 2, 3], (809904, 7315520)),
    ([1, 1, 3, 1, 1], (4616342, 85440832)),
    ([1, 1, 3, 2], (836136, 7154742)),
    ([1, 1, 4, 1], (588034, 7118960)),
    ([1, 1, 5], (73572, 454340)),
    ([1, 2, 1, 1, 1, 1], (27838346, 1465266704)),
    ([1, 2, 1, 1, 2], (4949520, 123494394)),
    ([1, 2, 1, 2, 1], (5046934, 126336544)),
    ([1, 2, 1, 3], (798720, 7346864)),
    ([1, 2, 2, 1, 1], (5186438, 123561520)),
    ([1, 2, 2, 2], (951752, 10159398)),
    ([1, 2, 3, 1], (854338, 7317248)),
    ([1, 2, 4], (104156, 599780)),
    ([1, 3, 1, 1, 1], (4627526, 85409488)),
    ([1, 3, 1, 2], (824952, 7186086)),
    ([1, 3, 2, 1], (854338, 7317248)),
    ([1, 3, 3], (133260, 436720)),
    ([1, 4, 1, 1], (588034, 7118960)),
    ([1, 4, 2], (107028, 597498)),
    ([1, 5, 1], (77642, 466336)),
    ([1, 6], (9330, 26068)),
    ([2, 1, 1, 1, 1, 1], (27376848, 1429956822)),
    ([2, 1, 1, 1, 2], (4867154, 120522810)),
    ([2, 1, 1, 2, 1], (4949520, 123494394)),
    ([2, 1, 1, 3], (783390, 7182076)),
    ([2, 1, 2, 1, 1], (4938336, 123525738)),
    ([2, 1, 2, 2], (907318, 10157670)),
    ([2, 1, 3, 1], (824952, 7186086)),
    ([2, 1, 4], (100086, 587784)),
    ([2, 2, 1, 1, 1], (5089024, 120719370)),
    ([2, 2, 1, 2], (907318, 10157670)),
    ([2, 2, 2, 1], (951752, 10159398)),
    ([2, 2, 3], (148590, 601508)),
    ([2, 3, 1, 1], (836136, 7154742)),
    ([2, 3, 2], (151462, 599226)),
    ([2, 4, 1], (107028, 597498)),
    ([2, 5], (13400, 38064)),
    ([3, 1, 1, 1, 1], (4405656, 85212928)),
    ([3, 1, 1, 2], (783390, 7182076)),
    ([3, 1, 2, 1], (798720, 7346864)),
    ([3, 1, 3], (126318, 427006)),
    ([3, 2, 1, 1], (809904, 7315520)),
    ([3, 2, 2], (148590, 601508)),
    ([3, 3, 1], (133260, 436720)),
    ([3, 4], (16272, 35782)),
    ([4, 1, 1, 1], (561520, 6985516)),
    ([4, 1, 2], (100086, 587784)),
    ([4, 2, 1], (104156, 599780)),
    ([4, 3], (16272, 35782)),
    ([5, 1, 1], (73572, 454340)),
    ([5, 2], (13400, 38064)),
    ([6, 1], (9330, 26068)),
    ([7], (1091, 1429))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_7 :
    censusRecords 7 = censusRecordsCached7 := by
  decide

private def censusRecordsCached8 : List (List ℕ × (ℤ × ℤ)) :=
  [
    ([1, 1, 1, 1, 1, 1, 1, 1], (2222627906, 485058147170)),
    ([1, 1, 1, 1, 1, 1, 2], (395153508, 40882871006)),
    ([1, 1, 1, 1, 1, 2, 1], (401815714, 41892399694)),
    ([1, 1, 1, 1, 1, 3], (63590702, 2436261788)),
    ([1, 1, 1, 1, 2, 1, 1], (399798238, 41971856830)),
    ([1, 1, 1, 1, 2, 2], (73453644, 3451410994)),
    ([1, 1, 1, 1, 3, 1], (66791438, 2441882306)),
    ([1, 1, 1, 1, 4], (8104714, 199718462)),
    ([1, 1, 1, 2, 1, 1, 1], (399631358, 41977197614)),
    ([1, 1, 1, 2, 1, 2], (71248956, 3532095954)),
    ([1, 1, 1, 2, 2, 1], (74828350, 3533120290)),
    ([1, 1, 1, 2, 3], (11685058, 209180180)),
    ([1, 1, 1, 3, 1, 1], (66604226, 2443110130)),
    ([1, 1, 1, 3, 2], (12063716, 204583998)),
    ([1, 1, 1, 4, 1], (8484322, 203559662)),
    ([1, 1, 1, 5], (1061518, 12991334)),
    ([1, 1, 2, 1, 1, 1, 1], (399798238, 41971856830)),
    ([1, 1, 2, 1, 1, 2], (71082076, 3537436738)),
    ([1, 1, 2, 1, 2, 1], (72480926, 3618849938)),
    ([1, 1, 2, 1, 3], (11470786, 210447940)),
    ([1, 1, 2, 2, 1, 1], (74498402, 3539392802)),
    ([1, 1, 2, 2, 2], (13671044, 291014318)),
    ([1, 1, 2, 3, 1], (12272194, 209601118)),
    ([1, 1, 2, 4], (1496174, 17180002)),
    ([1, 1, 3, 1, 1, 1], (66604226, 2443110130)),
    ([1, 1, 3, 1, 2], (11873588, 205555662)),
    ([1, 1, 3, 2, 1], (12296338, 209305022)),
    ([1, 1, 3, 3], (1917974, 12491980)),
    ([1, 1, 4, 1, 1], (8457262, 203599598)),
    ([1, 1, 4, 2], (1539316, 17088162)),
    ([1, 1, 5, 1], (1116566, 13338802)),
    ([1, 1, 6], (134158, 745738)),
    ([1, 2, 1, 1, 1, 1, 1], (401815714, 41892399694)),
    ([1, 2, 1, 1, 1, 2], (71436168, 3530868130)),
    ([1, 2, 1, 1, 2, 1], (72643994, 3617918210)),
    ([1, 2, 1, 1, 3], (11497846, 210408004)),
    ([1, 2, 1, 2, 1, 1], (72480926, 3618849938)),
    ([1, 2, 1, 2, 2], (13316952, 297582926)),
    ([1, 2, 1, 3, 1], (12109126, 210532846)),
    ([1, 2, 1, 4], (1469114, 17219938)),
    ([1, 2, 2, 1, 1, 1], (74828350, 3533120290)),
    ([1, 2, 2, 1, 2], (13341096, 297286830)),
    ([1, 2, 2, 2, 1], (13994870, 297336974)),
    ([1, 2, 2, 3], (2184914, 17604364)),
    ([1, 2, 3, 1, 1], (12296338, 209305022)),
    ([1, 2, 3, 2], (2227408, 17529666)),
    ([1, 2, 4, 1], (1573634, 17479522)),
    ([1, 2, 5], (197018, 1113658)),
    ([1, 3, 1, 1, 1, 1], (66791438, 2441882306)),
    ([1, 3, 1, 1, 2], (11876504, 205811822)),
    ([1, 3, 1, 2, 1], (12109126, 210532846)),
    ([1, 3, 1, 3], (1915058, 12235820)),
    ([1, 3, 2, 1, 1], (12272194, 209601118)),
    ([1, 3, 2, 2], (2251552, 17233570)),
    ([1, 3, 3, 1], (2018930, 12512546)),
    ([1, 3, 4], (246490, 1025774)),
    ([1, 4, 1, 1, 1], (8484322, 203559662)),
    ([1, 4, 1, 2], (1512256, 17128098)),
    ([1, 4, 2, 1], (1573634, 17479522)),
    ([1, 4, 3], (245842, 1042916)),
    ([1, 5, 1, 1], (1116566, 13338802)),
    ([1, 5, 2], (203348, 1117614)),
    ([1, 6, 1], (141970, 766190)),
    ([1, 7], (16640, 41918)),
    ([2, 1, 1, 1, 1, 1, 1], (395153508, 40882871006)),
    ([2, 1, 1, 1, 1, 2], (70252908, 3445790476)),
    ([2, 1, 1, 1, 2, 1], (71436168, 3530868130)),
    ([2, 1, 1, 1, 3], (11305450, 205338980)),
    ([2, 1, 1, 2, 1, 1], (71082076, 3537436738)),
    ([2, 1, 1, 2, 2], (13059764, 290889476)),
    ([2, 1, 1, 3, 1], (11876504, 205811822)),
    ([2, 1, 1, 4], (1441126, 16832534)),
    ([2, 1, 2, 1, 1, 1], (71248956, 3532095954)),
    ([2, 1, 2, 1, 2], (12702756, 297201924)),
    ([2, 1, 2, 2, 1], (13341096, 297286830)),
    ([2, 1, 2, 3], (2083310, 17600940)),
    ([2, 1, 3, 1, 1], (11873588, 205555662)),
    ([2, 1, 3, 2], (2150596, 17213004)),
    ([2, 1, 4, 1], (1512256, 17128098)),
    ([2, 1, 5], (189206, 1093206)),
    ([2, 2, 1, 1, 1, 1], (73453644, 3451410994)),
    ([2, 2, 1, 1, 2], (13059764, 290889476)),
    ([2, 2, 1, 2, 1], (13316952, 297582926)),
    ([2, 2, 1, 3], (2107454, 17304844)),
    ([2, 2, 2, 1, 1], (13671044, 291014318)),
    ([2, 2, 2, 2], (2508740, 23927020)),
    ([2, 2, 3, 1], (2251552, 17233570)),
    ([2, 2, 4], (274478, 1413178)),
    ([2, 3, 1, 1, 1], (12063716, 204583998)),
    ([2, 3, 1, 2], (2150596, 17213004)),
    ([2, 3, 2, 1], (2227408, 17529666)),
    ([2, 3, 3], (347446, 1046340)),
    ([2, 4, 1, 1], (1539316, 17088162)),
    ([2, 4, 2], (280160, 1434276)),
    ([2, 5, 1], (203348, 1117614)),
    ([2, 6], (24452, 62370)),
    ([3, 1, 1, 1, 1, 1], (63590702, 2436261788)),
    ([3, 1, 1, 1, 2], (11305450, 205338980)),
    ([3, 1, 1, 2, 1], (11497846, 210408004)),
    ([3, 1, 1, 3], (1819784, 12236352)),
    ([3, 1, 2, 1, 1], (11470786, 210447940)),
    ([3, 1, 2, 2], (2107454, 17304844)),
    ([3, 1, 3, 1], (1915058, 12235820)),
    ([3, 1, 4], (232348, 1001366)),
    ([3, 2, 1, 1, 1], (11685058, 209180180)),
    ([3, 2, 1, 2], (2083310, 17600940)),
    ([3, 2, 2, 1], (2184914, 17604364)),
    ([3, 2, 3], (341116, 1042384)),
    ([3, 3, 1, 1], (1917974, 12491980)),
    ([3, 3, 2], (347446, 1046340)),
    ([3, 4, 1], (245842, 1042916)),
    ([3, 5], (30782, 66326)),
    ([4, 1, 1, 1, 1], (8104714, 199718462)),
    ([4, 1, 1, 2], (1441126, 16832534)),
    ([4, 1, 2, 1], (1469114, 17219938)),
    ([4, 1, 3], (232348, 1001366)),
    ([4, 2, 1, 1], (1496174, 17180002)),
    ([4, 2, 2], (274478, 1413178)),
    ([4, 3, 1], (246490, 1025774)),
    ([4, 4], (30134, 83468)),
    ([5, 1, 1, 1], (1061518, 12991334)),
    ([5, 1, 2], (189206, 1093206)),
    ([5, 2, 1], (197018, 1113658)),
    ([5, 3], (30782, 66326)),
    ([6, 1, 1], (134158, 745738)),
    ([6, 2], (24452, 62370)),
    ([7, 1], (16640, 41918)),
    ([8], (1907, 2381))
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction identifies the full finite table with its actual determinant computation.
private theorem censusRecords_cached_8 :
    censusRecords 8 = censusRecordsCached8 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Finite comparisons over the certified literal tables are reduced in the kernel.
/-- Kernel-checked exhaustive comparison, using literals identified with actual
specialized Jacobi--Trudi determinants before the pair comparisons. -/
theorem censusRecords_collisions (N : ℕ) (hN : N ≤ 8) :
    ∀ x ∈ censusRecords N, ∀ y ∈ censusRecords N,
      x.2 = y.2 → y.1 = x.1 ∨ y.1 = x.1.reverse := by
  interval_cases N
  · rw [censusRecords_cached_0]
    decide
  · rw [censusRecords_cached_1]
    decide
  · rw [censusRecords_cached_2]
    decide
  · rw [censusRecords_cached_3]
    decide
  · rw [censusRecords_cached_4]
    decide
  · rw [censusRecords_cached_5]
    decide
  · rw [censusRecords_cached_6]
    decide
  · rw [censusRecords_cached_7]
    decide
  · rw [censusRecords_cached_8]
    decide

end SkewSchurReconstruction
