import PfaffianDescent.VoisinSmoothFourLineRoots
import PfaffianDescent.VoisinLinearChangeTripleIntersection

namespace PfaffianDescent

open MvPolynomial AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem exists_original_geometricEight_and_etale_quadratic_pair_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    let L := AlgebraicClosure K
    let p := (c.map (algebraMap K L)).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      (c.map (algebraMap K L))
    ∃ (z : Fin 8 → Fin 4 → L)
      (q r : MvPolynomial (Fin 4) L)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      Function.Surjective
        (homogeneousSectionRestriction (K := L)
          (fun (j : Fin 4) (i : Fin 8) => z i j) 2) ∧
      (∀ i, p.eval (z i) = 0 ∧ q.eval (z i) = 0 ∧ r.eval (z i) = 0) ∧
      (∀ i, z i ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ a : L, a • z i ≠ z j) ∧
      q ≠ 0 ∧ r ≠ 0 ∧
      LinearIndependent L
        ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩] ∧
      IsFinite (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ∧
      Etale (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  dsimp only
  obtain ⟨M, y, hM, hsurj, hzero, hquadrics, hy0, hdistinct, hdata⟩ :=
    exists_linear_change_geometricEight_and_standard_split_etale_of_smooth
      F hF hF0 c hc
  dsimp only at hdata
  obtain ⟨hfinite, hrank, hEtale⟩ := hdata
  let L : Type u := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  let ML : Matrix (Fin 4) (Fin 4) L := M.map f
  have hMLunit : IsUnit ML := Matrix.map_isUnit_of_isUnit_det f M hM
  have hMLdet : IsUnit ML.det :=
    (Matrix.isUnit_iff_isUnit_det ML).mp hMLunit
  let N : Matrix (Fin 4) (Fin 4) L := ML⁻¹
  have hNdet : IsUnit N.det := by
    exact Matrix.isUnit_nonsing_inv_det ML hMLdet
  let p : MvPolynomial (Fin 4) L := (c.map f).toMvPolynomial
  let pS : MvPolynomial (Fin 4) L := ((c.compLinear M).map f).toMvPolynomial
  let qS : MvPolynomial (Fin 4) L := X 1 * X 2
  let rS : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let q := linearSubstitution N qS
  let r := linearSubstitution N rS
  let z : Fin 8 → Fin 4 → L := fun i => ML.mulVec (y i)
  let hp := cubic_toMvPolynomial_isHomogeneous_three (c.map f)
  let hpS := cubic_toMvPolynomial_isHomogeneous_three ((c.compLinear M).map f)
  let hqS : qS.IsHomogeneous 2 :=
    (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hrS : rS.IsHomogeneous 2 :=
    (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
  let hq := linearSubstitution_homogeneous N hqS
  let hr := linearSubstitution_homogeneous N hrS
  have hzsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun (j : Fin 4) (i : Fin 8) => z i j) 2) :=
    homogeneousSectionRestriction_surjective_linearChange ML hMLdet y hsurj
  have hincidence : ∀ i,
      p.eval (z i) = 0 ∧ q.eval (z i) = 0 ∧ r.eval (z i) = 0 := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · exact (Cubic.compLinear_map_toMvPolynomial_eval f c M (y i)).symm.trans
        (hzero i)
    · exact (linearSubstitution_nonsing_inv_eval_mulVec ML hMLdet qS (y i)).trans
        (hquadrics i).1
    · exact (linearSubstitution_nonsing_inv_eval_mulVec ML hMLdet rS (y i)).trans
        (hquadrics i).2
  have hz0 : ∀ i, z i ≠ 0 :=
    linearChange_points_nonzero ML hMLunit (y := y) hy0
  have hzdistinct : ∀ i j, i ≠ j → ∀ a : L, a • z i ≠ z j :=
    linearChange_points_projectivelyDistinct ML hMLunit (y := y) hdistinct
  have hqS0 : qS ≠ 0 := by
    intro h
    exact (standard_split_quadric_pair_linearIndependent (L := L)).ne_zero 0
      (by change X 1 * X 2 = 0 at h; exact h)
  have hrS0 : rS ≠ 0 := by
    intro h
    exact (standard_split_quadric_pair_linearIndependent (L := L)).ne_zero 1
      (by change X 3 * (X 1 + X 2 + X 3) = 0 at h; exact h)
  have hq0 : q ≠ 0 := by
    intro h
    apply hqS0
    apply (linearSubstitutionEquiv N hNdet).injective
    change linearSubstitution N qS = linearSubstitution N 0
    simpa [q] using h
  have hr0 : r ≠ 0 := by
    intro h
    apply hrS0
    apply (linearSubstitutionEquiv N hNdet).injective
    change linearSubstitution N rS = linearSubstitution N 0
    simpa [r] using h
  have hlinPoly : LinearIndependent L ![q, r] := by
    have h := (standard_split_quadric_pair_linearIndependent (L := L)).map'
      (linearSubstitutionEquiv N hNdet).toLinearEquiv.toLinearMap
      (linearSubstitutionEquiv N hNdet).toLinearEquiv.ker
    have heq : (fun i => (linearSubstitutionEquiv N hNdet)
        (![qS, rS] i)) = ![q, r] := by
      funext i
      fin_cases i <;> rfl
    change LinearIndependent L (fun i =>
      (linearSubstitutionEquiv N hNdet) (![qS, rS] i)) at h
    rw [heq] at h
    exact h
  have hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩] :=
    homogeneous_quadric_pair_linearIndependent_of_polynomials
      q r hq hr hlinPoly
  have hEtale' := tripleCompleteIntersection_etale_linearSubstitution
    N hNdet pS qS rS hpS hqS hrS hEtale
  have hfinite' := tripleCompleteIntersection_isFinite_linearSubstitution
    N hNdet pS qS rS hpS hqS hrS hfinite
  have hpEq : linearSubstitution N pS = p := by
    exact Cubic.linearSubstitution_nonsing_inv_compLinear_map_toMvPolynomial
      f c M hMLdet
  have hIdeal :
      tripleCompleteIntersectionHomogeneousIdeal
          (linearSubstitution N pS) (linearSubstitution N qS)
          (linearSubstitution N rS)
          (linearSubstitution_homogeneous N hpS) hq hr =
        tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
    apply HomogeneousIdeal.ext
    change tripleCompleteIntersectionIdeal (linearSubstitution N pS)
        (linearSubstitution N qS) (linearSubstitution N rS) =
      tripleCompleteIntersectionIdeal p q r
    simpa [q, r] using congrArg
      (fun t => tripleCompleteIntersectionIdeal t
        (linearSubstitution N qS) (linearSubstitution N rS)) hpEq
  have hEtaleFinal : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rwa [hIdeal] at hEtale'
  have hfiniteFinal : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
    rwa [hIdeal] at hfinite'
  exact ⟨z, q, r, hq, hr, hzsurj, hincidence, hz0, hzdistinct,
    hq0, hr0, hlin, hfiniteFinal, hEtaleFinal⟩

end PfaffianDescent
