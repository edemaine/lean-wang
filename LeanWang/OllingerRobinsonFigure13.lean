/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Basic

/-!
Raw finite Wang-tile data extracted from Figure 13 of Jeandel and Vanier's
notes.

The figure draws each Wang edge as a small rendered pattern.  The natural
numbers below are identifiers for the distinct edge patterns in the rendered
Figure 13 tile grid, ordered by first occurrence while scanning tiles from top
to bottom and left to right.  An indexed rendering of this tile order is in
[figures/figure13-indexed.png](../figures/figure13-indexed.png), and named
Figure 16 layer components are in
[figures/figure16-layer-components.png](../figures/figure16-layer-components.png).
This module intentionally records only the raw Wang tiles; the scaffold roles
used by the reduction are added in the transcription layer once the
active/corner payload interpretation is fixed.
-/

namespace LeanWang
namespace OllingerRobinson

private def t (n s e w : Nat) : WangTile where
  n := n
  s := s
  e := e
  w := w

/-- Raw Figure 13 scaffold tiles, scanned top-to-bottom and left-to-right. -/
def fig13Tiles : TileSet := [
  t 0 1 2 3,
  t 4 5 6 7,
  t 8 9 10 11,
  t 12 13 14 15,
  t 16 17 18 19,
  t 20 21 22 23,
  t 24 25 26 27,
  t 28 29 30 31,
  t 32 28 33 14,
  t 34 35 11 36,
  t 37 24 15 38,
  t 39 13 40 41,
  t 42 16 36 43,
  t 44 20 45 46,
  t 47 24 23 48,
  t 49 17 50 51,
  t 33 35 15 52,
  t 45 28 53 54,
  t 55 5 31 56,
  t 57 29 58 59,
  t 60 28 33 10,
  t 61 35 15 62,
  t 63 24 23 64,
  t 65 13 66 67,
  t 68 13 36 69,
  t 70 16 71 48,
  t 72 20 45 73,
  t 45 24 74 75,
  t 76 29 58 77,
  t 78 13 79 80,
  t 81 16 71 82,
  t 83 20 84 73,
  t 85 50 2 86,
  t 87 88 14 89,
  t 90 11 91 92,
  t 93 94 23 48,
  t 95 50 96 97,
  t 98 33 99 48,
  t 100 53 101 102,
  t 103 31 66 104,
  t 105 106 15 107,
  t 45 96 71 108,
  t 109 110 84 111,
  t 112 66 58 113,
  t 114 50 2 86,
  t 115 116 23 117,
  t 118 50 91 119,
  t 120 14 121 75,
  t 122 84 99 97,
  t 33 50 79 80,
  t 123 124 2 86,
  t 125 45 101 102,
  t 112 126 99 127,
  t 103 128 129 107,
  t 130 45 71 131,
  t 132 133 99 134,
  t 113 135 136 137,
  t 138 97 139 119,
  t 140 15 43 141,
  t 142 45 143 104,
  t 144 129 15 107,
  t 145 100 79 80,
  t 146 30 33 141,
  t 147 45 148 119,
  t 149 66 14 111,
  t 150 100 66 151,
  t 152 31 91 153,
  t 154 30 58 155,
  t 156 50 79 131,
  t 118 157 40 158,
  t 159 31 91 160,
  t 161 53 50 162,
  t 163 102 140 164,
  t 138 107 139 165,
  t 166 58 50 104,
  t 167 102 91 168,
  t 145 40 15 119,
  t 112 40 148 137,
  t 78 30 99 137,
  t 161 79 140 164,
  t 163 113 136 137,
  t 138 50 139 158,
  t 123 113 58 137,
  t 164 100 136 158,
  t 161 30 15 158,
  t 112 50 139 137,
  t 164 30 91 137,
  t 161 31 140 164,
  t 167 148 23 137,
  t 164 107 136 137,
  t 143 113 2 158,
  t 138 104 43 137
]

@[simp]
theorem fig13Tiles_length : fig13Tiles.length = 92 := by
  decide

theorem fig13Tiles_nodup : fig13Tiles.Nodup := by
  decide

end OllingerRobinson
end LeanWang
