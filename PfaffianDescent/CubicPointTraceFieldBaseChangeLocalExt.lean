import PfaffianDescent.CubicPointTraceFieldBaseChangeFlatScalars
import PfaffianDescent.ScalarExtensionBasis
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Native local Ext under actual flat scalar extension -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual tensor functor along the actual flat local-ring map is exact. -/
theorem cubicPointTraceFieldBaseChangeLocalScalarsPreservesFiniteLimits
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (hg : g.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g) := by
  letI := cubicPointTraceFieldBaseChangeFlatScalarsPreservesMonomorphisms g hg
  letI : (ModuleCat.extendScalars.{u, u, u} g).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

section
variable {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (hg : g.Flat)
  [HasExt.{u + 1} (ModuleCat.{u} R)] [HasExt.{u + 1} (ModuleCat.{u} S)]

/-- Native local Ext maps along the actual functor `S ⊗[R] -`. -/
def cubicPointTraceFieldBaseChangeLocalExtMap (M N : ModuleCat.{u} R) (n : ℕ) :
    Ext.{u + 1} M N n →+
      Ext.{u + 1} ((ModuleCat.extendScalars.{u, u, u} g).obj M)
        ((ModuleCat.extendScalars.{u, u, u} g).obj N) n := by
  letI := cubicPointTraceFieldBaseChangeLocalScalarsPreservesFiniteLimits g hg
  exact (ModuleCat.extendScalars.{u, u, u} g).mapExtAddHom M N n

/-- Flat tensor pullback commutes with each actual source morphism. -/
theorem cubicPointTraceFieldBaseChangeLocalExtMap_precomp
    {A B N : ModuleCat.{u} R} (v : A ⟶ B) (n : ℕ) (z : Ext.{u + 1} B N n) :
    cubicPointTraceFieldBaseChangeLocalExtMap g hg A N n
        ((Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) v).comp z (zero_add n)) =
      (Ext.mk₀.{u + 1} (C := ModuleCat.{u} S) ((ModuleCat.extendScalars g).map v)).comp
        (cubicPointTraceFieldBaseChangeLocalExtMap g hg B N n z) (zero_add n) := by
  letI := cubicPointTraceFieldBaseChangeLocalScalarsPreservesFiniteLimits g hg
  change ((Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) v).comp z (zero_add n)).mapExactFunctor
      (ModuleCat.extendScalars.{u, u, u} g) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rfl

/-- Zero source precomposition remains zero under actual flat tensor pullback. -/
theorem cubicPointTraceFieldBaseChangeLocalExtMap_precomp_eq_zero
    {A B N : ModuleCat.{u} R} (v : A ⟶ B) (n : ℕ) (z : Ext.{u + 1} B N n)
    (hz : (Ext.mk₀.{u + 1} (C := ModuleCat.{u} R) v).comp z (zero_add n) = 0) :
    (Ext.mk₀.{u + 1} (C := ModuleCat.{u} S) ((ModuleCat.extendScalars g).map v)).comp
      (cubicPointTraceFieldBaseChangeLocalExtMap g hg B N n z) (zero_add n) = 0 := by
  rw [← cubicPointTraceFieldBaseChangeLocalExtMap_precomp g hg v n z, hz, map_zero]

end
end PfaffianDescent
