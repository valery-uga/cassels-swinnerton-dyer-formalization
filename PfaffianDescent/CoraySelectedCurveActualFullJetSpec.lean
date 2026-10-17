import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint
import PfaffianDescent.CorayGroundProjectiveCurveLocalDefect
import PfaffianDescent.SchemeModuleOriginalBaseStalkResidueTower
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Algebra.Algebra.Prod

/-! SOURCE ONLY / UNVERIFIED. Actual normalized polynomial jets construct
a closed immersion from their full-jet spectrum to the actual pair curve.
Its OWN native image stalk surjects onto the jet, with proved original-K
coefficient compatibility. Identification of this image with packet002's
AX by exact residue reduction is still separate, not supplied or claimed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem normalizedAffineEquation_rename_succAbove
    {K : Type u} [Field K] (anchor : Fin 4) (f : MvPolynomial (Fin 3) K) :
    normalizedAffineEquation anchor (MvPolynomial.rename anchor.succAbove f) = f := by
  have hcomp : (normalizedAffineEquation (M := K) anchor).comp
      (MvPolynomial.rename anchor.succAbove) = AlgHom.id K (MvPolynomial (Fin 3) K) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [normalizedAffineEquation]
  exact AlgHom.congr_fun hcomp f

/-- The actual original-K projective full-jet evaluation is surjective.
Only generating residue coordinates are used, already derived at the
canonical cubic closed point by the actual boundary selector. -/
theorem normalizedOriginalFullJet_evaluation_surjective
    {K M : Type u} [Field K] [CharZero K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    (p : MvPolynomial (Fin 4) K) (anchor : Fin 4) (x : Fin 4 → M)
    (hx : x anchor = 1) (pivot : Fin 3)
    (heval : Function.Surjective (eval₂Hom (algebraMap K M)
      (fun r => x (anchor.succAbove r)))) :
    Function.Surjective (eval₂Hom (algebraMap K (PfaffianDescent.CubicSurfaceFirstJet M))
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet
        (p.map (algebraMap K M)) anchor x pivot)) := by
  intro a
  obtain ⟨f, hf⟩ := groundAffineSurfaceJetMap_surjective
    (normalizedAffineEquation anchor p) (fun r => x (anchor.succAbove r)) pivot heval a
  refine ⟨MvPolynomial.rename anchor.succAbove f, ?_⟩
  have h := normalizedGroundAffineEquation_jet_evaluation p
    (MvPolynomial.rename anchor.succAbove f) anchor x hx pivot
  rw [normalizedAffineEquation_rename_succAbove] at h
  rw [IsScalarTower.algebraMap_eq K M (PfaffianDescent.CubicSurfaceFirstJet M)]
  exact h.symm.trans hf

private def actualFullJetLocalRing (M : Type u) [Field M] :
    IsLocalRing (PfaffianDescent.CubicSurfaceFirstJet M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst with h | h
    · exact Or.inl (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h)
    · exact Or.inr (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
        (by simpa only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using h))

/-- Actual selected q full-jet vanishing and smooth pivot construct an
actual closed full-jet immersion into the literal selected curve. The
surjective native map is from that image point's OWN stalk. It carries the
independently original base constants to the SAME jet constants.
No desired jet surjectivity, native comparison, GI or nonregularity premise. -/
theorem selectedCurve_exists_actualFullJet_closedImmersion_nativeStalk
    {K M : Type u} [Field K] [CharZero K] [Field M] [Algebra K M]
    [FiniteDimensional K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hqhom : q.IsHomogeneous n)
    (anchor : Fin 4) (x : Fin 4 → M) (hx : x anchor = 1) (pivot : Fin 3)
    (hpzero : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv (anchor.succAbove pivot) p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : q.eval₂ ((algebraMap M (PfaffianDescent.CubicSurfaceFirstJet M)).comp
      (algebraMap K M)) (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet
        (p.map (algebraMap K M)) anchor x pivot) = 0)
    (heval : Function.Surjective (eval₂Hom (algebraMap K M)
      (fun r => x (anchor.succAbove r)))) :
    let B := PfaffianDescent.CubicSurfaceFirstJet M
    letI := actualFullJetLocalRing M
    let J := projectiveIntersectionIdeal p q hp hqhom
    ∃ r : Spec (.of B) ⟶ scheme J,
      IsClosedImmersion r ∧
      r ≫ toBase J = Spec.map (CommRingCat.ofHom (algebraMap K B)) ∧
      IsClosed ({r (IsLocalRing.closedPoint B)} : Set (scheme J)) ∧
      Function.Surjective (Scheme.stalkClosedPointTo r).hom ∧
      (Scheme.stalkClosedPointTo r).hom.comp
        (schemeStalkBaseRingHom (toBase J) (r (IsLocalRing.closedPoint B))) =
          algebraMap K B ∧
      ∃ (heM : ∀ a ∈ J.toIdeal, (eval₂Hom (algebraMap K M) x) a = 0)
        (hOneM : (Ideal.Quotient.lift J.toIdeal (eval₂Hom (algebraMap K M) x) heM)
          (coordinate J anchor) = 1),
        linearNormalizedPointAt J x heM (coordinate J anchor)
          (coordinate_mem J anchor) hOneM =
            Spec.map (CommRingCat.ofHom
              (TrivSqZeroExt.fstHom K M (Fin 2 → M)).toRingHom) ≫ r := by
  classical
  intro B
  letI := actualFullJetLocalRing M
  intro J
  let τ : Fin 4 → B := PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet
    (p.map (algebraMap K M)) anchor x pivot
  have hτanchor : τ anchor = 1 := by
    simp [τ, PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet,
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row, hx]
  have hpjet : p.eval₂ (algebraMap K B) τ = 0 := by
    have h := groundAffineSurfaceJetMap_equation_zero (normalizedAffineEquation anchor p)
      (fun r => x (anchor.succAbove r)) pivot
      ((normalizedGroundAffineEquation_evaluation p anchor x hx).trans hpzero)
      (by rwa [normalizedGroundAffineEquation_partial_evaluation p anchor x hx pivot])
    rw [normalizedGroundAffineEquation_jet_evaluation p p anchor x hx pivot] at h
    simpa only [IsScalarTower.algebraMap_eq K M B] using h
  have hqjet : q.eval₂ (algebraMap K B) τ = 0 := by
    simpa only [IsScalarTower.algebraMap_eq K M B] using hq
  have hspan : J.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K B) τ) := by
    rw [projectiveIntersectionIdeal_toIdeal]
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hpjet
    · obtain rfl := Set.mem_singleton_iff.mp ha
      exact hqjet
  have heJ : ∀ a ∈ J.toIdeal, (eval₂Hom (algebraMap K B) τ) a = 0 :=
    fun a ha => hspan ha
  have hOne : (Ideal.Quotient.lift J.toIdeal (eval₂Hom (algebraMap K B) τ) heJ)
      (coordinate J anchor) = 1 := by
    change (eval₂Hom (algebraMap K B) τ) (X anchor) = 1
    simpa only [eval₂Hom_X'] using hτanchor
  let r := linearNormalizedPointAt J τ heJ (coordinate J anchor)
    (coordinate_mem J anchor) hOne
  letI : Module.Finite K B := by
    change Module.Finite K (M × (Fin 2 → M))
    infer_instance
  letI : IsClosedImmersion r := linearNormalizedPointAt_isClosedImmersion J τ heJ
    (coordinate J anchor) (coordinate_mem J anchor) hOne
    (normalizedOriginalFullJet_evaluation_surjective p anchor x hx pivot heval)
  have hrbase : r ≫ toBase J = Spec.map (CommRingCat.ofHom (algebraMap K B)) :=
    linearNormalizedPointAt_toBase J τ heJ (coordinate J anchor) (coordinate_mem J anchor) hOne
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo r).hom := by
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of B)).hom).2.comp
      (r.stalkMap_surjective (IsLocalRing.closedPoint B))
  have hclosed : IsClosed ({r (IsLocalRing.closedPoint B)} : Set (scheme J)) := by
    rw [← Set.image_singleton]
    exact r.isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint B)
  refine ⟨r, inferInstance, hrbase, hclosed, hsurj, ?_, ?_⟩
  · have hcat : CommRingCat.ofHom
        (schemeStalkBaseRingHom (toBase J) (r (IsLocalRing.closedPoint B))) ≫
          Scheme.stalkClosedPointTo r = CommRingCat.ofHom (algebraMap K B) := by
      apply Spec.map_injective
      rw [Spec.map_comp, schemeStalkBaseRingHom_spec, ← Category.assoc,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hrbase]
    exact congrArg CommRingCat.Hom.hom hcat
  · let ρ := TrivSqZeroExt.fstHom K M (Fin 2 → M)
    have hres : ρ.toRingHom.comp (eval₂Hom (algebraMap K B) τ) =
        eval₂Hom (algebraMap K M) x := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, eval₂Hom_C]
        change ρ (algebraMap K (TrivSqZeroExt M (Fin 2 → M)) c) = algebraMap K M c
        exact ρ.commutes c
      · intro j
        simp [ρ, τ, PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet]
    have heM : ∀ a ∈ J.toIdeal, (eval₂Hom (algebraMap K M) x) a = 0 := by
      intro a ha
      rw [← hres, RingHom.comp_apply, heJ a ha, map_zero]
    have hOneM : (Ideal.Quotient.lift J.toIdeal (eval₂Hom (algebraMap K M) x) heM)
        (coordinate J anchor) = 1 := by
      change (eval₂Hom (algebraMap K M) x) (X anchor) = 1
      simpa only [eval₂Hom_X'] using hx
    refine ⟨heM, hOneM, ?_⟩
    exact linearNormalizedPointAt_naturality J τ heJ ρ x
      (fun j => by
        change x j = (τ j).fst
        simp only [τ, PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet,
          TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero])
      heM (coordinate J anchor) (coordinate_mem J anchor) hOne hOneM

end PfaffianDescent.Coray
