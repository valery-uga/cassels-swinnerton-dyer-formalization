import PfaffianDescent.CubicPointTraceFieldBaseChangeFlatPullback
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Actual native Ext pullback along a flat scheme morphism

The exactness used below is proved for the actual geometric pullback. In
particular, a zero unit-precomposition class remains zero after pullback.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  [HasExt.{u} Y.Modules] [HasExt.{u} X.Modules]

/-- The actual exact geometric pullback map on native scheme-module Ext. -/
def cubicPointTraceFieldBaseChangeFlatPullbackExtMap
    (M N : Y.Modules) (n : ℕ) :
    Ext.{u} M N n →+
      Ext.{u} ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) n :=
  (Scheme.Modules.pullback f).mapExtAddHom M N n

/-- Actual pullback commutes with precomposition by an actual degree-zero
morphism, in all native Ext degrees. -/
theorem cubicPointTraceFieldBaseChangeFlatPullbackExtMap_precomp
    {A B N : Y.Modules} (v : A ⟶ B) (n : ℕ) (z : Ext.{u} B N n) :
    cubicPointTraceFieldBaseChangeFlatPullbackExtMap f A N n
        ((Ext.mk₀.{u} (C := Y.Modules) v).comp z (zero_add n)) =
      (Ext.mk₀.{u} (C := X.Modules) ((Scheme.Modules.pullback f).map v)).comp
        (cubicPointTraceFieldBaseChangeFlatPullbackExtMap f B N n z) (zero_add n) := by
  change ((Ext.mk₀.{u} (C := Y.Modules) v).comp z (zero_add n)).mapExactFunctor
      (Scheme.Modules.pullback f) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rfl

/-- A zero precomposition class pulls back to zero under the actual
geometric functor; no trace or cohomological base-change square is assumed. -/
theorem cubicPointTraceFieldBaseChangeFlatPullbackExtMap_precomp_eq_zero
    {A B N : Y.Modules} (v : A ⟶ B) (n : ℕ) (z : Ext.{u} B N n)
    (hz : (Ext.mk₀.{u} (C := Y.Modules) v).comp z (zero_add n) = 0) :
    (Ext.mk₀.{u} (C := X.Modules) ((Scheme.Modules.pullback f).map v)).comp
      (cubicPointTraceFieldBaseChangeFlatPullbackExtMap f B N n z) (zero_add n) = 0 := by
  rw [← cubicPointTraceFieldBaseChangeFlatPullbackExtMap_precomp f v n z, hz, map_zero]

end
end PfaffianDescent
