import AllCharacteristics.LaurentPencilGenericCubic
import AllCharacteristics.FiniteFieldPointExplicitPushforward
import AllCharacteristics.OriginalSmoothPointPrescribedPowerLaurentLift
import AllCharacteristics.CoprimeEffectiveCycle

/-! SOURCE ONLY / UNVERIFIED. Actual prescribed lift → literal residue-
weighted cycle of degree [L:k] → actual degree-three line cycle → Bézout. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open HomogeneousProjective
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem prescribedOriginalSmoothPoint_generic_explicitCycle
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hp0 : p ≠ 0)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hsm : q (closedPoint L) ∈ (hypersurfaceToBase p hp).smoothLocus) :
    ∃ a : Spec (.of (LaurentSeries L)) ⟶
        hypersurface (prescribedLaurentGenericEquation p g)
          (prescribedLaurentGenericEquation_homogeneous hp hg),
      ∃ ha : a ≫ hypersurfaceToBase (prescribedLaurentGenericEquation p g)
          (prescribedLaurentGenericEquation_homogeneous hp hg) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (LaurentSeries k) (LaurentSeries L))),
      ∃ ζ : EffectiveZeroCycle (hypersurface (prescribedLaurentGenericEquation p g)
          (prescribedLaurentGenericEquation_homogeneous hp hg)),
        ζ = finiteFieldPointExplicitCycle
          (hypersurfaceToBase (prescribedLaurentGenericEquation p g)
            (prescribedLaurentGenericEquation_homogeneous hp hg)) a ha ∧
        EffectiveZeroCycle.degree
          (hypersurfaceToBase (prescribedLaurentGenericEquation p g)
            (prescribedLaurentGenericEquation_homogeneous hp hg)) ζ = Module.finrank k L := by
  obtain ⟨s, hs, hred, y, hys, hy, hdeg⟩ :=
    prescribedOriginalSmoothPoint_powerLaurent_lift_and_degree p g hp hg hp0 q hq hsm
  let a := y ≫ (prescribedLaurentGenericCubicIso p g hp hg).inv
  have ha : a ≫ hypersurfaceToBase (prescribedLaurentGenericEquation p g)
      (prescribedLaurentGenericEquation_homogeneous hp hg) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (LaurentSeries k) (LaurentSeries L))) := by
    dsimp only [a]
    rw [Category.assoc, prescribedLaurentGenericCubicIso_inv_base, hy]
    rfl
  refine ⟨a, ha, finiteFieldPointExplicitCycle _ a ha, rfl, ?_⟩
  exact (finiteFieldPointExplicitCycle_degree _ a ha).trans hdeg

/-- The reference degree three is an ACTUAL line intersection over k((t)).
That field is internally proved infinite, even when the original k is finite. -/
theorem prescribedOriginalSmoothPoint_generic_degreeOne_cycle
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hp0 : p ≠ 0) (hg0 : g ≠ 0)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hsm : q (closedPoint L) ∈ (hypersurfaceToBase p hp).smoothLocus)
    (hdegree : Nat.Coprime (Module.finrank k L) 3) :
    ∃ w : ZeroCycle (hypersurface (prescribedLaurentGenericEquation p g)
        (prescribedLaurentGenericEquation_homogeneous hp hg)),
      ZeroCycle.degree
        (hypersurfaceToBase (prescribedLaurentGenericEquation p g)
          (prescribedLaurentGenericEquation_homogeneous hp hg)) w = 1 := by
  obtain ⟨a, ha, ζ, hζ, hdeg⟩ :=
    prescribedOriginalSmoothPoint_generic_explicitCycle p g hp hg hp0 q hq hsm
  letI : Infinite (LaurentSeries k) := laurentCoefficientField_infinite
  obtain ⟨z₃, hz₃⟩ := hypersurface_exists_lineSection_effective_degree_three
    (by decide : 2 ≤ 4) (prescribedLaurentGenericEquation p g)
    (prescribedLaurentGenericEquation_homogeneous hp hg)
    (prescribedLaurentGenericEquation_ne_zero hg0)
  apply ZeroCycle.exists_degree_one_of_coprime_degree _ ζ.toZeroCycle z₃.toZeroCycle
    (Module.finrank k L)
  · rw [EffectiveZeroCycle.degree_toZeroCycle, hdeg]
  · rw [EffectiveZeroCycle.degree_toZeroCycle, hz₃]
    rfl
  · exact hdegree

end AllCharacteristics
