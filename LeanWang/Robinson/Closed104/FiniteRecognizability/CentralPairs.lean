/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6
-/
import LeanWang.Robinson.Closed104.FiniteRecognizability.PhaseRows
import Mathlib.Tactic.FinCases

/-!
# Kernel-certified central row pairs

The cached pairs equal the vertical compatibility search, bucket by bucket.
-/

set_option maxRecDepth 30000

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace FiniteRecognizability

def rowsVCompatible (table : List (List Index))
    (lower upper : List Index) : Bool :=
  (lower.zip upper).all fun pair =>
    decide (pair.2 ∈ followersAt table pair.1)

private def indexPairs (pairs : List (List Nat × List Nat)) : List (List Index × List Index) :=
  pairs.map fun p =>
    (p.1.map (fun n => ⟨n % 104, Nat.mod_lt _ (by decide)⟩),
     p.2.map (fun n => ⟨n % 104, Nat.mod_lt _ (by decide)⟩))

private def centralPairTable : List (List (List Index × List Index)) :=
  ([
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [([8, 32, 24, 32], [5, 74, 4, 76]), ([8, 32, 24, 42], [5, 74, 4, 64]), ([8, 32, 24, 48], [5, 74, 4, 70]), ([8, 32, 24, 83], [5, 74, 4, 58]), ([8, 32, 24, 89], [5, 74, 4, 64]), ([8, 32, 24, 95], [5, 74, 4, 70]), ([8, 32, 24, 101], [5, 74, 4, 76]), ([8, 42, 24, 32], [5, 62, 4, 76]), ([8, 42, 24, 42], [5, 62, 4, 64]), ([8, 42, 24, 48], [5, 62, 4, 70]), ([8, 42, 24, 83], [5, 62, 4, 58]), ([8, 42, 24, 89], [5, 62, 4, 64]), ([8, 42, 24, 95], [5, 62, 4, 70]), ([8, 42, 24, 101], [5, 62, 4, 76]), ([8, 48, 24, 32], [5, 68, 4, 76]), ([8, 48, 24, 42], [5, 68, 4, 64]), ([8, 48, 24, 48], [5, 68, 4, 70]), ([8, 48, 24, 83], [5, 68, 4, 58]), ([8, 48, 24, 89], [5, 68, 4, 64]), ([8, 48, 24, 95], [5, 68, 4, 70]), ([8, 48, 24, 101], [5, 68, 4, 76]), ([8, 83, 25, 33], [5, 56, 4, 76]), ([8, 83, 25, 38], [5, 56, 4, 58]), ([8, 83, 25, 49], [5, 56, 4, 70]), ([8, 84, 25, 33], [5, 57, 4, 76]), ([8, 84, 25, 38], [5, 57, 4, 58]), ([8, 84, 25, 49], [5, 57, 4, 70]), ([8, 89, 25, 33], [5, 62, 4, 76]), ([8, 89, 25, 38], [5, 62, 4, 58]), ([8, 89, 25, 49], [5, 62, 4, 70]), ([8, 90, 25, 33], [5, 63, 4, 76]), ([8, 90, 25, 38], [5, 63, 4, 58]), ([8, 90, 25, 49], [5, 63, 4, 70]), ([8, 95, 25, 33], [5, 68, 4, 76]), ([8, 95, 25, 38], [5, 68, 4, 58]), ([8, 95, 25, 49], [5, 68, 4, 70]), ([8, 96, 25, 33], [5, 69, 4, 76]), ([8, 96, 25, 38], [5, 69, 4, 58]), ([8, 96, 25, 49], [5, 69, 4, 70]), ([8, 101, 25, 33], [5, 74, 4, 76]), ([8, 101, 25, 38], [5, 74, 4, 58]), ([8, 101, 25, 49], [5, 74, 4, 70]), ([8, 102, 25, 33], [5, 75, 4, 76]), ([8, 102, 25, 38], [5, 75, 4, 58]), ([8, 102, 25, 49], [5, 75, 4, 70])],
  [([9, 2, 26, 34], [5, 69, 4, 76]), ([9, 2, 26, 43], [5, 69, 4, 64]), ([9, 2, 26, 50], [5, 69, 4, 70]), ([9, 33, 25, 33], [5, 74, 4, 76]), ([9, 33, 25, 38], [5, 74, 4, 58]), ([9, 33, 25, 49], [5, 74, 4, 70]), ([9, 38, 25, 33], [5, 56, 4, 76]), ([9, 38, 25, 38], [5, 56, 4, 58]), ([9, 38, 25, 49], [5, 56, 4, 70]), ([9, 49, 25, 33], [5, 68, 4, 76]), ([9, 49, 25, 38], [5, 68, 4, 58]), ([9, 49, 25, 49], [5, 68, 4, 70])],
  [([10, 34, 26, 34], [5, 74, 4, 76]), ([10, 34, 26, 43], [5, 74, 4, 64]), ([10, 34, 26, 50], [5, 74, 4, 70]), ([10, 43, 26, 34], [5, 62, 4, 76]), ([10, 43, 26, 43], [5, 62, 4, 64]), ([10, 43, 26, 50], [5, 62, 4, 70]), ([10, 50, 26, 34], [5, 68, 4, 76]), ([10, 50, 26, 43], [5, 68, 4, 64]), ([10, 50, 26, 50], [5, 68, 4, 70]), ([10, 85, 27, 35], [5, 57, 4, 76]), ([10, 85, 27, 39], [5, 57, 4, 58]), ([10, 85, 27, 51], [5, 57, 4, 70]), ([10, 91, 27, 35], [5, 63, 4, 76]), ([10, 91, 27, 39], [5, 63, 4, 58]), ([10, 91, 27, 51], [5, 63, 4, 70]), ([10, 97, 27, 35], [5, 69, 4, 76]), ([10, 97, 27, 39], [5, 69, 4, 58]), ([10, 97, 27, 51], [5, 69, 4, 70]), ([10, 103, 27, 35], [5, 75, 4, 76]), ([10, 103, 27, 39], [5, 75, 4, 58]), ([10, 103, 27, 51], [5, 75, 4, 70])],
  [([11, 3, 24, 32], [5, 75, 4, 76]), ([11, 3, 24, 42], [5, 75, 4, 64]), ([11, 3, 24, 48], [5, 75, 4, 70]), ([11, 3, 24, 83], [5, 75, 4, 58]), ([11, 3, 24, 89], [5, 75, 4, 64]), ([11, 3, 24, 95], [5, 75, 4, 70]), ([11, 3, 24, 101], [5, 75, 4, 76]), ([11, 35, 27, 35], [5, 74, 4, 76]), ([11, 35, 27, 39], [5, 74, 4, 58]), ([11, 35, 27, 51], [5, 74, 4, 70]), ([11, 39, 27, 35], [5, 56, 4, 76]), ([11, 39, 27, 39], [5, 56, 4, 58]), ([11, 39, 27, 51], [5, 56, 4, 70]), ([11, 51, 27, 35], [5, 68, 4, 76]), ([11, 51, 27, 39], [5, 68, 4, 58]), ([11, 51, 27, 51], [5, 68, 4, 70])],
  [([12, 0, 17, 41], [6, 61, 7, 65]), ([12, 0, 17, 46], [6, 61, 7, 71]), ([12, 0, 17, 54], [6, 61, 7, 77]), ([12, 0, 17, 82], [6, 61, 7, 59]), ([12, 0, 17, 88], [6, 61, 7, 65]), ([12, 0, 17, 94], [6, 61, 7, 71]), ([12, 0, 17, 100], [6, 61, 7, 77])],
  [([13, 1, 16, 40], [6, 67, 7, 65]), ([13, 1, 16, 44], [6, 67, 7, 71]), ([13, 1, 16, 52], [6, 67, 7, 77]), ([13, 1, 16, 80], [6, 67, 7, 59]), ([13, 1, 16, 81], [6, 67, 7, 60]), ([13, 1, 16, 86], [6, 67, 7, 65]), ([13, 1, 16, 87], [6, 67, 7, 66]), ([13, 1, 16, 92], [6, 67, 7, 71]), ([13, 1, 16, 93], [6, 67, 7, 72]), ([13, 1, 16, 98], [6, 67, 7, 77]), ([13, 1, 16, 99], [6, 67, 7, 78])],
  [([14, 2, 19, 34], [6, 73, 7, 77]), ([14, 2, 19, 43], [6, 73, 7, 65]), ([14, 2, 19, 50], [6, 73, 7, 71]), ([14, 2, 19, 85], [6, 73, 7, 60]), ([14, 2, 19, 91], [6, 73, 7, 66]), ([14, 2, 19, 97], [6, 73, 7, 72]), ([14, 2, 19, 103], [6, 73, 7, 78])],
  [([15, 3, 18, 32], [6, 79, 7, 77]), ([15, 3, 18, 42], [6, 79, 7, 65]), ([15, 3, 18, 48], [6, 79, 7, 71]), ([15, 3, 18, 83], [6, 79, 7, 59]), ([15, 3, 18, 84], [6, 79, 7, 60]), ([15, 3, 18, 89], [6, 79, 7, 65]), ([15, 3, 18, 90], [6, 79, 7, 66]), ([15, 3, 18, 95], [6, 79, 7, 71]), ([15, 3, 18, 96], [6, 79, 7, 72]), ([15, 3, 18, 101], [6, 79, 7, 77]), ([15, 3, 18, 102], [6, 79, 7, 78])],
  [([16, 80, 12, 0], [7, 59, 6, 61]), ([16, 81, 12, 0], [7, 60, 6, 61]), ([16, 86, 12, 0], [7, 65, 6, 61]), ([16, 87, 12, 0], [7, 66, 6, 61]), ([16, 92, 12, 0], [7, 71, 6, 61]), ([16, 93, 12, 0], [7, 72, 6, 61]), ([16, 98, 12, 0], [7, 77, 6, 61]), ([16, 99, 12, 0], [7, 78, 6, 61])],
  [([17, 82, 13, 1], [7, 59, 6, 67]), ([17, 88, 13, 1], [7, 65, 6, 67]), ([17, 94, 13, 1], [7, 71, 6, 67]), ([17, 100, 13, 1], [7, 77, 6, 67])],
  [([18, 83, 14, 2], [7, 59, 6, 73]), ([18, 84, 14, 2], [7, 60, 6, 73]), ([18, 89, 14, 2], [7, 65, 6, 73]), ([18, 90, 14, 2], [7, 66, 6, 73]), ([18, 95, 14, 2], [7, 71, 6, 73]), ([18, 96, 14, 2], [7, 72, 6, 73]), ([18, 101, 14, 2], [7, 77, 6, 73]), ([18, 102, 14, 2], [7, 78, 6, 73])],
  [([19, 85, 15, 3], [7, 60, 6, 79]), ([19, 91, 15, 3], [7, 66, 6, 79]), ([19, 97, 15, 3], [7, 72, 6, 79]), ([19, 103, 15, 3], [7, 78, 6, 79])],
  [([20, 40, 28, 40], [4, 64, 5, 62]), ([20, 40, 28, 44], [4, 64, 5, 68]), ([20, 40, 28, 52], [4, 64, 5, 74]), ([20, 40, 28, 80], [4, 64, 5, 56]), ([20, 40, 28, 81], [4, 64, 5, 57]), ([20, 40, 28, 86], [4, 64, 5, 62]), ([20, 40, 28, 87], [4, 64, 5, 63]), ([20, 40, 28, 92], [4, 64, 5, 68]), ([20, 40, 28, 93], [4, 64, 5, 69]), ([20, 40, 28, 98], [4, 64, 5, 74]), ([20, 40, 28, 99], [4, 64, 5, 75]), ([20, 44, 28, 40], [4, 70, 5, 62]), ([20, 44, 28, 44], [4, 70, 5, 68]), ([20, 44, 28, 52], [4, 70, 5, 74]), ([20, 44, 28, 80], [4, 70, 5, 56]), ([20, 44, 28, 81], [4, 70, 5, 57]), ([20, 44, 28, 86], [4, 70, 5, 62]), ([20, 44, 28, 87], [4, 70, 5, 63]), ([20, 44, 28, 92], [4, 70, 5, 68]), ([20, 44, 28, 93], [4, 70, 5, 69]), ([20, 44, 28, 98], [4, 70, 5, 74]), ([20, 44, 28, 99], [4, 70, 5, 75]), ([20, 52, 28, 40], [4, 76, 5, 62]), ([20, 52, 28, 44], [4, 76, 5, 68]), ([20, 52, 28, 52], [4, 76, 5, 74]), ([20, 52, 28, 80], [4, 76, 5, 56]), ([20, 52, 28, 81], [4, 76, 5, 57]), ([20, 52, 28, 86], [4, 76, 5, 62]), ([20, 52, 28, 87], [4, 76, 5, 63]), ([20, 52, 28, 92], [4, 76, 5, 68]), ([20, 52, 28, 93], [4, 76, 5, 69]), ([20, 52, 28, 98], [4, 76, 5, 74]), ([20, 52, 28, 99], [4, 76, 5, 75]), ([20, 80, 29, 0], [4, 58, 5, 57]), ([20, 80, 29, 36], [4, 58, 5, 56]), ([20, 80, 29, 45], [4, 58, 5, 68]), ([20, 80, 29, 53], [4, 58, 5, 74]), ([20, 86, 29, 0], [4, 64, 5, 57]), ([20, 86, 29, 36], [4, 64, 5, 56]), ([20, 86, 29, 45], [4, 64, 5, 68]), ([20, 86, 29, 53], [4, 64, 5, 74]), ([20, 92, 29, 0], [4, 70, 5, 57]), ([20, 92, 29, 36], [4, 70, 5, 56]), ([20, 92, 29, 45], [4, 70, 5, 68]), ([20, 92, 29, 53], [4, 70, 5, 74]), ([20, 98, 29, 0], [4, 76, 5, 57]), ([20, 98, 29, 36], [4, 76, 5, 56]), ([20, 98, 29, 45], [4, 76, 5, 68]), ([20, 98, 29, 53], [4, 76, 5, 74])],
  [([21, 36, 29, 0], [4, 58, 5, 57]), ([21, 36, 29, 36], [4, 58, 5, 56]), ([21, 36, 29, 45], [4, 58, 5, 68]), ([21, 36, 29, 53], [4, 58, 5, 74]), ([21, 45, 29, 0], [4, 70, 5, 57]), ([21, 45, 29, 36], [4, 70, 5, 56]), ([21, 45, 29, 45], [4, 70, 5, 68]), ([21, 45, 29, 53], [4, 70, 5, 74]), ([21, 53, 29, 0], [4, 76, 5, 57]), ([21, 53, 29, 36], [4, 76, 5, 56]), ([21, 53, 29, 45], [4, 76, 5, 68]), ([21, 53, 29, 53], [4, 76, 5, 74])],
  [([22, 41, 30, 41], [4, 64, 5, 62]), ([22, 41, 30, 46], [4, 64, 5, 68]), ([22, 41, 30, 54], [4, 64, 5, 74]), ([22, 41, 30, 82], [4, 64, 5, 56]), ([22, 41, 30, 88], [4, 64, 5, 62]), ([22, 41, 30, 94], [4, 64, 5, 68]), ([22, 41, 30, 100], [4, 64, 5, 74]), ([22, 46, 30, 41], [4, 70, 5, 62]), ([22, 46, 30, 46], [4, 70, 5, 68]), ([22, 46, 30, 54], [4, 70, 5, 74]), ([22, 46, 30, 82], [4, 70, 5, 56]), ([22, 46, 30, 88], [4, 70, 5, 62]), ([22, 46, 30, 94], [4, 70, 5, 68]), ([22, 46, 30, 100], [4, 70, 5, 74]), ([22, 54, 30, 41], [4, 76, 5, 62]), ([22, 54, 30, 46], [4, 76, 5, 68]), ([22, 54, 30, 54], [4, 76, 5, 74]), ([22, 54, 30, 82], [4, 76, 5, 56]), ([22, 54, 30, 88], [4, 76, 5, 62]), ([22, 54, 30, 94], [4, 76, 5, 68]), ([22, 54, 30, 100], [4, 76, 5, 74]), ([22, 82, 31, 1], [4, 58, 5, 63]), ([22, 82, 31, 37], [4, 58, 5, 56]), ([22, 82, 31, 47], [4, 58, 5, 68]), ([22, 82, 31, 55], [4, 58, 5, 74]), ([22, 88, 31, 1], [4, 64, 5, 63]), ([22, 88, 31, 37], [4, 64, 5, 56]), ([22, 88, 31, 47], [4, 64, 5, 68]), ([22, 88, 31, 55], [4, 64, 5, 74]), ([22, 94, 31, 1], [4, 70, 5, 63]), ([22, 94, 31, 37], [4, 70, 5, 56]), ([22, 94, 31, 47], [4, 70, 5, 68]), ([22, 94, 31, 55], [4, 70, 5, 74]), ([22, 100, 31, 1], [4, 76, 5, 63]), ([22, 100, 31, 37], [4, 76, 5, 56]), ([22, 100, 31, 47], [4, 76, 5, 68]), ([22, 100, 31, 55], [4, 76, 5, 74])],
  [([23, 37, 31, 1], [4, 58, 5, 63]), ([23, 37, 31, 37], [4, 58, 5, 56]), ([23, 37, 31, 47], [4, 58, 5, 68]), ([23, 37, 31, 55], [4, 58, 5, 74]), ([23, 47, 31, 1], [4, 70, 5, 63]), ([23, 47, 31, 37], [4, 70, 5, 56]), ([23, 47, 31, 47], [4, 70, 5, 68]), ([23, 47, 31, 55], [4, 70, 5, 74]), ([23, 55, 31, 1], [4, 76, 5, 63]), ([23, 55, 31, 37], [4, 76, 5, 56]), ([23, 55, 31, 47], [4, 76, 5, 68]), ([23, 55, 31, 55], [4, 76, 5, 74])],
  [([24, 32, 8, 32], [4, 76, 5, 74]), ([24, 32, 8, 42], [4, 76, 5, 62]), ([24, 32, 8, 48], [4, 76, 5, 68]), ([24, 32, 8, 83], [4, 76, 5, 56]), ([24, 32, 8, 84], [4, 76, 5, 57]), ([24, 32, 8, 89], [4, 76, 5, 62]), ([24, 32, 8, 90], [4, 76, 5, 63]), ([24, 32, 8, 95], [4, 76, 5, 68]), ([24, 32, 8, 96], [4, 76, 5, 69]), ([24, 32, 8, 101], [4, 76, 5, 74]), ([24, 32, 8, 102], [4, 76, 5, 75]), ([24, 42, 8, 32], [4, 64, 5, 74]), ([24, 42, 8, 42], [4, 64, 5, 62]), ([24, 42, 8, 48], [4, 64, 5, 68]), ([24, 42, 8, 83], [4, 64, 5, 56]), ([24, 42, 8, 84], [4, 64, 5, 57]), ([24, 42, 8, 89], [4, 64, 5, 62]), ([24, 42, 8, 90], [4, 64, 5, 63]), ([24, 42, 8, 95], [4, 64, 5, 68]), ([24, 42, 8, 96], [4, 64, 5, 69]), ([24, 42, 8, 101], [4, 64, 5, 74]), ([24, 42, 8, 102], [4, 64, 5, 75]), ([24, 48, 8, 32], [4, 70, 5, 74]), ([24, 48, 8, 42], [4, 70, 5, 62]), ([24, 48, 8, 48], [4, 70, 5, 68]), ([24, 48, 8, 83], [4, 70, 5, 56]), ([24, 48, 8, 84], [4, 70, 5, 57]), ([24, 48, 8, 89], [4, 70, 5, 62]), ([24, 48, 8, 90], [4, 70, 5, 63]), ([24, 48, 8, 95], [4, 70, 5, 68]), ([24, 48, 8, 96], [4, 70, 5, 69]), ([24, 48, 8, 101], [4, 70, 5, 74]), ([24, 48, 8, 102], [4, 70, 5, 75]), ([24, 83, 9, 2], [4, 58, 5, 69]), ([24, 83, 9, 33], [4, 58, 5, 74]), ([24, 83, 9, 38], [4, 58, 5, 56]), ([24, 83, 9, 49], [4, 58, 5, 68]), ([24, 89, 9, 2], [4, 64, 5, 69]), ([24, 89, 9, 33], [4, 64, 5, 74]), ([24, 89, 9, 38], [4, 64, 5, 56]), ([24, 89, 9, 49], [4, 64, 5, 68]), ([24, 95, 9, 2], [4, 70, 5, 69]), ([24, 95, 9, 33], [4, 70, 5, 74]), ([24, 95, 9, 38], [4, 70, 5, 56]), ([24, 95, 9, 49], [4, 70, 5, 68]), ([24, 101, 9, 2], [4, 76, 5, 69]), ([24, 101, 9, 33], [4, 76, 5, 74]), ([24, 101, 9, 38], [4, 76, 5, 56]), ([24, 101, 9, 49], [4, 76, 5, 68])],
  [([25, 33, 9, 2], [4, 76, 5, 69]), ([25, 33, 9, 33], [4, 76, 5, 74]), ([25, 33, 9, 38], [4, 76, 5, 56]), ([25, 33, 9, 49], [4, 76, 5, 68]), ([25, 38, 9, 2], [4, 58, 5, 69]), ([25, 38, 9, 33], [4, 58, 5, 74]), ([25, 38, 9, 38], [4, 58, 5, 56]), ([25, 38, 9, 49], [4, 58, 5, 68]), ([25, 49, 9, 2], [4, 70, 5, 69]), ([25, 49, 9, 33], [4, 70, 5, 74]), ([25, 49, 9, 38], [4, 70, 5, 56]), ([25, 49, 9, 49], [4, 70, 5, 68])],
  [([26, 34, 10, 34], [4, 76, 5, 74]), ([26, 34, 10, 43], [4, 76, 5, 62]), ([26, 34, 10, 50], [4, 76, 5, 68]), ([26, 34, 10, 85], [4, 76, 5, 57]), ([26, 34, 10, 91], [4, 76, 5, 63]), ([26, 34, 10, 97], [4, 76, 5, 69]), ([26, 34, 10, 103], [4, 76, 5, 75]), ([26, 43, 10, 34], [4, 64, 5, 74]), ([26, 43, 10, 43], [4, 64, 5, 62]), ([26, 43, 10, 50], [4, 64, 5, 68]), ([26, 43, 10, 85], [4, 64, 5, 57]), ([26, 43, 10, 91], [4, 64, 5, 63]), ([26, 43, 10, 97], [4, 64, 5, 69]), ([26, 43, 10, 103], [4, 64, 5, 75]), ([26, 50, 10, 34], [4, 70, 5, 74]), ([26, 50, 10, 43], [4, 70, 5, 62]), ([26, 50, 10, 50], [4, 70, 5, 68]), ([26, 50, 10, 85], [4, 70, 5, 57]), ([26, 50, 10, 91], [4, 70, 5, 63]), ([26, 50, 10, 97], [4, 70, 5, 69]), ([26, 50, 10, 103], [4, 70, 5, 75])],
  [([27, 35, 11, 3], [4, 76, 5, 75]), ([27, 35, 11, 35], [4, 76, 5, 74]), ([27, 35, 11, 39], [4, 76, 5, 56]), ([27, 35, 11, 51], [4, 76, 5, 68]), ([27, 39, 11, 3], [4, 58, 5, 75]), ([27, 39, 11, 35], [4, 58, 5, 74]), ([27, 39, 11, 39], [4, 58, 5, 56]), ([27, 39, 11, 51], [4, 58, 5, 68]), ([27, 51, 11, 3], [4, 70, 5, 75]), ([27, 51, 11, 35], [4, 70, 5, 74]), ([27, 51, 11, 39], [4, 70, 5, 56]), ([27, 51, 11, 51], [4, 70, 5, 68])],
  [([28, 40, 20, 40], [5, 62, 4, 64]), ([28, 40, 20, 44], [5, 62, 4, 70]), ([28, 40, 20, 52], [5, 62, 4, 76]), ([28, 40, 20, 80], [5, 62, 4, 58]), ([28, 40, 20, 86], [5, 62, 4, 64]), ([28, 40, 20, 92], [5, 62, 4, 70]), ([28, 40, 20, 98], [5, 62, 4, 76]), ([28, 44, 20, 40], [5, 68, 4, 64]), ([28, 44, 20, 44], [5, 68, 4, 70]), ([28, 44, 20, 52], [5, 68, 4, 76]), ([28, 44, 20, 80], [5, 68, 4, 58]), ([28, 44, 20, 86], [5, 68, 4, 64]), ([28, 44, 20, 92], [5, 68, 4, 70]), ([28, 44, 20, 98], [5, 68, 4, 76]), ([28, 52, 20, 40], [5, 74, 4, 64]), ([28, 52, 20, 44], [5, 74, 4, 70]), ([28, 52, 20, 52], [5, 74, 4, 76]), ([28, 52, 20, 80], [5, 74, 4, 58]), ([28, 52, 20, 86], [5, 74, 4, 64]), ([28, 52, 20, 92], [5, 74, 4, 70]), ([28, 52, 20, 98], [5, 74, 4, 76]), ([28, 80, 21, 36], [5, 56, 4, 58]), ([28, 80, 21, 45], [5, 56, 4, 70]), ([28, 80, 21, 53], [5, 56, 4, 76]), ([28, 81, 21, 36], [5, 57, 4, 58]), ([28, 81, 21, 45], [5, 57, 4, 70]), ([28, 81, 21, 53], [5, 57, 4, 76]), ([28, 86, 21, 36], [5, 62, 4, 58]), ([28, 86, 21, 45], [5, 62, 4, 70]), ([28, 86, 21, 53], [5, 62, 4, 76]), ([28, 87, 21, 36], [5, 63, 4, 58]), ([28, 87, 21, 45], [5, 63, 4, 70]), ([28, 87, 21, 53], [5, 63, 4, 76]), ([28, 92, 21, 36], [5, 68, 4, 58]), ([28, 92, 21, 45], [5, 68, 4, 70]), ([28, 92, 21, 53], [5, 68, 4, 76]), ([28, 93, 21, 36], [5, 69, 4, 58]), ([28, 93, 21, 45], [5, 69, 4, 70]), ([28, 93, 21, 53], [5, 69, 4, 76]), ([28, 98, 21, 36], [5, 74, 4, 58]), ([28, 98, 21, 45], [5, 74, 4, 70]), ([28, 98, 21, 53], [5, 74, 4, 76]), ([28, 99, 21, 36], [5, 75, 4, 58]), ([28, 99, 21, 45], [5, 75, 4, 70]), ([28, 99, 21, 53], [5, 75, 4, 76])],
  [([29, 0, 22, 41], [5, 57, 4, 64]), ([29, 0, 22, 46], [5, 57, 4, 70]), ([29, 0, 22, 54], [5, 57, 4, 76]), ([29, 0, 22, 82], [5, 57, 4, 58]), ([29, 0, 22, 88], [5, 57, 4, 64]), ([29, 0, 22, 94], [5, 57, 4, 70]), ([29, 0, 22, 100], [5, 57, 4, 76]), ([29, 36, 21, 36], [5, 56, 4, 58]), ([29, 36, 21, 45], [5, 56, 4, 70]), ([29, 36, 21, 53], [5, 56, 4, 76]), ([29, 45, 21, 36], [5, 68, 4, 58]), ([29, 45, 21, 45], [5, 68, 4, 70]), ([29, 45, 21, 53], [5, 68, 4, 76]), ([29, 53, 21, 36], [5, 74, 4, 58]), ([29, 53, 21, 45], [5, 74, 4, 70]), ([29, 53, 21, 53], [5, 74, 4, 76])],
  [([30, 41, 22, 41], [5, 62, 4, 64]), ([30, 41, 22, 46], [5, 62, 4, 70]), ([30, 41, 22, 54], [5, 62, 4, 76]), ([30, 41, 22, 82], [5, 62, 4, 58]), ([30, 41, 22, 88], [5, 62, 4, 64]), ([30, 41, 22, 94], [5, 62, 4, 70]), ([30, 41, 22, 100], [5, 62, 4, 76]), ([30, 46, 22, 41], [5, 68, 4, 64]), ([30, 46, 22, 46], [5, 68, 4, 70]), ([30, 46, 22, 54], [5, 68, 4, 76]), ([30, 46, 22, 82], [5, 68, 4, 58]), ([30, 46, 22, 88], [5, 68, 4, 64]), ([30, 46, 22, 94], [5, 68, 4, 70]), ([30, 46, 22, 100], [5, 68, 4, 76]), ([30, 54, 22, 41], [5, 74, 4, 64]), ([30, 54, 22, 46], [5, 74, 4, 70]), ([30, 54, 22, 54], [5, 74, 4, 76]), ([30, 54, 22, 82], [5, 74, 4, 58]), ([30, 54, 22, 88], [5, 74, 4, 64]), ([30, 54, 22, 94], [5, 74, 4, 70]), ([30, 54, 22, 100], [5, 74, 4, 76]), ([30, 82, 23, 37], [5, 56, 4, 58]), ([30, 82, 23, 47], [5, 56, 4, 70]), ([30, 82, 23, 55], [5, 56, 4, 76]), ([30, 88, 23, 37], [5, 62, 4, 58]), ([30, 88, 23, 47], [5, 62, 4, 70]), ([30, 88, 23, 55], [5, 62, 4, 76]), ([30, 94, 23, 37], [5, 68, 4, 58]), ([30, 94, 23, 47], [5, 68, 4, 70]), ([30, 94, 23, 55], [5, 68, 4, 76]), ([30, 100, 23, 37], [5, 74, 4, 58]), ([30, 100, 23, 47], [5, 74, 4, 70]), ([30, 100, 23, 55], [5, 74, 4, 76])],
  [([31, 1, 20, 40], [5, 63, 4, 64]), ([31, 1, 20, 44], [5, 63, 4, 70]), ([31, 1, 20, 52], [5, 63, 4, 76]), ([31, 1, 20, 80], [5, 63, 4, 58]), ([31, 1, 20, 86], [5, 63, 4, 64]), ([31, 1, 20, 92], [5, 63, 4, 70]), ([31, 1, 20, 98], [5, 63, 4, 76]), ([31, 37, 23, 37], [5, 56, 4, 58]), ([31, 37, 23, 47], [5, 56, 4, 70]), ([31, 37, 23, 55], [5, 56, 4, 76]), ([31, 47, 23, 37], [5, 68, 4, 58]), ([31, 47, 23, 47], [5, 68, 4, 70]), ([31, 47, 23, 55], [5, 68, 4, 76]), ([31, 55, 23, 37], [5, 74, 4, 58]), ([31, 55, 23, 47], [5, 74, 4, 70]), ([31, 55, 23, 55], [5, 74, 4, 76])],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []] : List (List (List Nat × List Nat))).map indexPairs

private def centralPairsFrom (first : Index) : List (List Index × List Index) :=
  centralPairTable[first.val]?.getD []

private theorem centralPairsFrom_row0 :
    centralPairsFrom 0 =
      (southRowsFrom 0).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row1 :
    centralPairsFrom 1 =
      (southRowsFrom 1).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row2 :
    centralPairsFrom 2 =
      (southRowsFrom 2).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row3 :
    centralPairsFrom 3 =
      (southRowsFrom 3).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row4 :
    centralPairsFrom 4 =
      (southRowsFrom 4).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row5 :
    centralPairsFrom 5 =
      (southRowsFrom 5).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row6 :
    centralPairsFrom 6 =
      (southRowsFrom 6).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row7 :
    centralPairsFrom 7 =
      (southRowsFrom 7).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row8 :
    centralPairsFrom 8 =
      (southRowsFrom 8).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row9 :
    centralPairsFrom 9 =
      (southRowsFrom 9).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row10 :
    centralPairsFrom 10 =
      (southRowsFrom 10).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row11 :
    centralPairsFrom 11 =
      (southRowsFrom 11).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row12 :
    centralPairsFrom 12 =
      (southRowsFrom 12).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row13 :
    centralPairsFrom 13 =
      (southRowsFrom 13).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row14 :
    centralPairsFrom 14 =
      (southRowsFrom 14).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row15 :
    centralPairsFrom 15 =
      (southRowsFrom 15).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row16 :
    centralPairsFrom 16 =
      (southRowsFrom 16).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row17 :
    centralPairsFrom 17 =
      (southRowsFrom 17).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row18 :
    centralPairsFrom 18 =
      (southRowsFrom 18).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row19 :
    centralPairsFrom 19 =
      (southRowsFrom 19).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row20 :
    centralPairsFrom 20 =
      (southRowsFrom 20).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row21 :
    centralPairsFrom 21 =
      (southRowsFrom 21).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row22 :
    centralPairsFrom 22 =
      (southRowsFrom 22).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row23 :
    centralPairsFrom 23 =
      (southRowsFrom 23).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row24 :
    centralPairsFrom 24 =
      (southRowsFrom 24).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row25 :
    centralPairsFrom 25 =
      (southRowsFrom 25).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row26 :
    centralPairsFrom 26 =
      (southRowsFrom 26).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row27 :
    centralPairsFrom 27 =
      (southRowsFrom 27).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row28 :
    centralPairsFrom 28 =
      (southRowsFrom 28).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row29 :
    centralPairsFrom 29 =
      (southRowsFrom 29).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row30 :
    centralPairsFrom 30 =
      (southRowsFrom 30).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row31 :
    centralPairsFrom 31 =
      (southRowsFrom 31).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row32 :
    centralPairsFrom 32 =
      (southRowsFrom 32).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row33 :
    centralPairsFrom 33 =
      (southRowsFrom 33).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row34 :
    centralPairsFrom 34 =
      (southRowsFrom 34).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row35 :
    centralPairsFrom 35 =
      (southRowsFrom 35).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row36 :
    centralPairsFrom 36 =
      (southRowsFrom 36).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row37 :
    centralPairsFrom 37 =
      (southRowsFrom 37).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row38 :
    centralPairsFrom 38 =
      (southRowsFrom 38).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row39 :
    centralPairsFrom 39 =
      (southRowsFrom 39).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row40 :
    centralPairsFrom 40 =
      (southRowsFrom 40).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row41 :
    centralPairsFrom 41 =
      (southRowsFrom 41).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row42 :
    centralPairsFrom 42 =
      (southRowsFrom 42).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row43 :
    centralPairsFrom 43 =
      (southRowsFrom 43).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row44 :
    centralPairsFrom 44 =
      (southRowsFrom 44).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row45 :
    centralPairsFrom 45 =
      (southRowsFrom 45).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row46 :
    centralPairsFrom 46 =
      (southRowsFrom 46).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row47 :
    centralPairsFrom 47 =
      (southRowsFrom 47).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row48 :
    centralPairsFrom 48 =
      (southRowsFrom 48).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row49 :
    centralPairsFrom 49 =
      (southRowsFrom 49).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row50 :
    centralPairsFrom 50 =
      (southRowsFrom 50).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row51 :
    centralPairsFrom 51 =
      (southRowsFrom 51).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row52 :
    centralPairsFrom 52 =
      (southRowsFrom 52).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row53 :
    centralPairsFrom 53 =
      (southRowsFrom 53).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row54 :
    centralPairsFrom 54 =
      (southRowsFrom 54).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row55 :
    centralPairsFrom 55 =
      (southRowsFrom 55).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row56 :
    centralPairsFrom 56 =
      (southRowsFrom 56).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row57 :
    centralPairsFrom 57 =
      (southRowsFrom 57).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row58 :
    centralPairsFrom 58 =
      (southRowsFrom 58).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row59 :
    centralPairsFrom 59 =
      (southRowsFrom 59).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row60 :
    centralPairsFrom 60 =
      (southRowsFrom 60).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row61 :
    centralPairsFrom 61 =
      (southRowsFrom 61).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row62 :
    centralPairsFrom 62 =
      (southRowsFrom 62).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row63 :
    centralPairsFrom 63 =
      (southRowsFrom 63).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row64 :
    centralPairsFrom 64 =
      (southRowsFrom 64).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row65 :
    centralPairsFrom 65 =
      (southRowsFrom 65).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row66 :
    centralPairsFrom 66 =
      (southRowsFrom 66).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row67 :
    centralPairsFrom 67 =
      (southRowsFrom 67).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row68 :
    centralPairsFrom 68 =
      (southRowsFrom 68).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row69 :
    centralPairsFrom 69 =
      (southRowsFrom 69).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row70 :
    centralPairsFrom 70 =
      (southRowsFrom 70).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row71 :
    centralPairsFrom 71 =
      (southRowsFrom 71).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row72 :
    centralPairsFrom 72 =
      (southRowsFrom 72).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row73 :
    centralPairsFrom 73 =
      (southRowsFrom 73).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row74 :
    centralPairsFrom 74 =
      (southRowsFrom 74).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row75 :
    centralPairsFrom 75 =
      (southRowsFrom 75).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row76 :
    centralPairsFrom 76 =
      (southRowsFrom 76).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row77 :
    centralPairsFrom 77 =
      (southRowsFrom 77).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row78 :
    centralPairsFrom 78 =
      (southRowsFrom 78).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row79 :
    centralPairsFrom 79 =
      (southRowsFrom 79).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row80 :
    centralPairsFrom 80 =
      (southRowsFrom 80).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row81 :
    centralPairsFrom 81 =
      (southRowsFrom 81).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row82 :
    centralPairsFrom 82 =
      (southRowsFrom 82).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row83 :
    centralPairsFrom 83 =
      (southRowsFrom 83).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row84 :
    centralPairsFrom 84 =
      (southRowsFrom 84).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row85 :
    centralPairsFrom 85 =
      (southRowsFrom 85).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row86 :
    centralPairsFrom 86 =
      (southRowsFrom 86).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row87 :
    centralPairsFrom 87 =
      (southRowsFrom 87).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row88 :
    centralPairsFrom 88 =
      (southRowsFrom 88).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row89 :
    centralPairsFrom 89 =
      (southRowsFrom 89).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row90 :
    centralPairsFrom 90 =
      (southRowsFrom 90).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row91 :
    centralPairsFrom 91 =
      (southRowsFrom 91).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row92 :
    centralPairsFrom 92 =
      (southRowsFrom 92).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row93 :
    centralPairsFrom 93 =
      (southRowsFrom 93).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row94 :
    centralPairsFrom 94 =
      (southRowsFrom 94).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row95 :
    centralPairsFrom 95 =
      (southRowsFrom 95).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row96 :
    centralPairsFrom 96 =
      (southRowsFrom 96).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row97 :
    centralPairsFrom 97 =
      (southRowsFrom 97).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row98 :
    centralPairsFrom 98 =
      (southRowsFrom 98).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row99 :
    centralPairsFrom 99 =
      (southRowsFrom 99).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row100 :
    centralPairsFrom 100 =
      (southRowsFrom 100).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row101 :
    centralPairsFrom 101 =
      (southRowsFrom 101).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row102 :
    centralPairsFrom 102 =
      (southRowsFrom 102).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_row103 :
    centralPairsFrom 103 =
      (southRowsFrom 103).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  decide +kernel

private theorem centralPairsFrom_correct (first : Index) :
    centralPairsFrom first =
      (southRowsFrom first).flatMap (fun south =>
        (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
          (fun north => (south, north))) := by
  fin_cases first
  · exact centralPairsFrom_row0
  · exact centralPairsFrom_row1
  · exact centralPairsFrom_row2
  · exact centralPairsFrom_row3
  · exact centralPairsFrom_row4
  · exact centralPairsFrom_row5
  · exact centralPairsFrom_row6
  · exact centralPairsFrom_row7
  · exact centralPairsFrom_row8
  · exact centralPairsFrom_row9
  · exact centralPairsFrom_row10
  · exact centralPairsFrom_row11
  · exact centralPairsFrom_row12
  · exact centralPairsFrom_row13
  · exact centralPairsFrom_row14
  · exact centralPairsFrom_row15
  · exact centralPairsFrom_row16
  · exact centralPairsFrom_row17
  · exact centralPairsFrom_row18
  · exact centralPairsFrom_row19
  · exact centralPairsFrom_row20
  · exact centralPairsFrom_row21
  · exact centralPairsFrom_row22
  · exact centralPairsFrom_row23
  · exact centralPairsFrom_row24
  · exact centralPairsFrom_row25
  · exact centralPairsFrom_row26
  · exact centralPairsFrom_row27
  · exact centralPairsFrom_row28
  · exact centralPairsFrom_row29
  · exact centralPairsFrom_row30
  · exact centralPairsFrom_row31
  · exact centralPairsFrom_row32
  · exact centralPairsFrom_row33
  · exact centralPairsFrom_row34
  · exact centralPairsFrom_row35
  · exact centralPairsFrom_row36
  · exact centralPairsFrom_row37
  · exact centralPairsFrom_row38
  · exact centralPairsFrom_row39
  · exact centralPairsFrom_row40
  · exact centralPairsFrom_row41
  · exact centralPairsFrom_row42
  · exact centralPairsFrom_row43
  · exact centralPairsFrom_row44
  · exact centralPairsFrom_row45
  · exact centralPairsFrom_row46
  · exact centralPairsFrom_row47
  · exact centralPairsFrom_row48
  · exact centralPairsFrom_row49
  · exact centralPairsFrom_row50
  · exact centralPairsFrom_row51
  · exact centralPairsFrom_row52
  · exact centralPairsFrom_row53
  · exact centralPairsFrom_row54
  · exact centralPairsFrom_row55
  · exact centralPairsFrom_row56
  · exact centralPairsFrom_row57
  · exact centralPairsFrom_row58
  · exact centralPairsFrom_row59
  · exact centralPairsFrom_row60
  · exact centralPairsFrom_row61
  · exact centralPairsFrom_row62
  · exact centralPairsFrom_row63
  · exact centralPairsFrom_row64
  · exact centralPairsFrom_row65
  · exact centralPairsFrom_row66
  · exact centralPairsFrom_row67
  · exact centralPairsFrom_row68
  · exact centralPairsFrom_row69
  · exact centralPairsFrom_row70
  · exact centralPairsFrom_row71
  · exact centralPairsFrom_row72
  · exact centralPairsFrom_row73
  · exact centralPairsFrom_row74
  · exact centralPairsFrom_row75
  · exact centralPairsFrom_row76
  · exact centralPairsFrom_row77
  · exact centralPairsFrom_row78
  · exact centralPairsFrom_row79
  · exact centralPairsFrom_row80
  · exact centralPairsFrom_row81
  · exact centralPairsFrom_row82
  · exact centralPairsFrom_row83
  · exact centralPairsFrom_row84
  · exact centralPairsFrom_row85
  · exact centralPairsFrom_row86
  · exact centralPairsFrom_row87
  · exact centralPairsFrom_row88
  · exact centralPairsFrom_row89
  · exact centralPairsFrom_row90
  · exact centralPairsFrom_row91
  · exact centralPairsFrom_row92
  · exact centralPairsFrom_row93
  · exact centralPairsFrom_row94
  · exact centralPairsFrom_row95
  · exact centralPairsFrom_row96
  · exact centralPairsFrom_row97
  · exact centralPairsFrom_row98
  · exact centralPairsFrom_row99
  · exact centralPairsFrom_row100
  · exact centralPairsFrom_row101
  · exact centralPairsFrom_row102
  · exact centralPairsFrom_row103

def centralRowPairs : List (List Index × List Index) := indices.flatMap centralPairsFrom

theorem centralRowPairs_correct : centralRowPairs =
    southCentralRows.flatMap (fun south =>
      (northCentralRows.filter (fun north => rowsVCompatible vFollowerTable south north)).map
        (fun north => (south, north))) := by
  unfold centralRowPairs southCentralRows
  rw [List.flatMap_assoc]
  apply congrArg (fun f : Index → List (List Index × List Index) => indices.flatMap f)
  funext first
  exact centralPairsFrom_correct first

end FiniteRecognizability
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
