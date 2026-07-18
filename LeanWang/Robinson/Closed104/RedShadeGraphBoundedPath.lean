/-
Copyright (c) 2026 lean-wang contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5
-/
import LeanWang.Robinson.Closed104.RedShadeGraph

/-! Red-graph paths whose intermediate ports stay in a finite box. -/

namespace LeanWang
namespace OllingerRobinson
namespace Figure13Layers
namespace Closed104
namespace RedShadeGraphBoundedPath

open RedShadeGraph

def PortInBounds (port : Port) (width height : Nat) : Prop :=
  port.x < width ∧ port.y < height

inductive BoundedPath (indexGrid : Nat → Nat → Index)
    (width height : Nat) : Port → Port → Bool → Prop where
  | refl (port : Port) (hport : PortInBounds port width height) :
      BoundedPath indexGrid width height port port false
  | ofLink {first second : Port} {parity : Bool}
      (link : Link indexGrid first second parity)
      (hfirst : PortInBounds first width height)
      (hsecond : PortInBounds second width height) :
      BoundedPath indexGrid width height first second parity
  | trans {first second third : Port} {firstParity secondParity : Bool}
      (firstPath : BoundedPath indexGrid width height
        first second firstParity)
      (secondPath : BoundedPath indexGrid width height
        second third secondParity) :
      BoundedPath indexGrid width height first third
        (Bool.xor firstParity secondParity)

theorem BoundedPath.path
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    Path indexGrid first second parity := by
  induction path with
  | refl port _ => exact Path.refl port
  | ofLink link _ _ => exact Path.ofLink link
  | trans _ _ firstIH secondIH => exact Path.trans firstIH secondIH

theorem BoundedPath.first_inBounds
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    PortInBounds first width height := by
  induction path with
  | refl _ hport => exact hport
  | ofLink _ hfirst _ => exact hfirst
  | trans _ _ firstIH _ => exact firstIH

theorem BoundedPath.second_inBounds
    {indexGrid : Nat → Nat → Index} {width height : Nat}
    {first second : Port} {parity : Bool}
    (path : BoundedPath indexGrid width height first second parity) :
    PortInBounds second width height := by
  induction path with
  | refl _ hport => exact hport
  | ofLink _ _ hsecond => exact hsecond
  | trans _ _ _ secondIH => exact secondIH

end RedShadeGraphBoundedPath
end Closed104
end Figure13Layers
end OllingerRobinson
end LeanWang
