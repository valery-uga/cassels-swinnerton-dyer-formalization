import PfaffianDescent.CubicFullJetEvaluationMinorOpen

/-!
Actual cubic interpolation at every field-valued point of the full-jet
determinant open. The inverse minor constructs the interpolating cubic;
no interpolation certificate is required at the new field point.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.UniversalHomogeneous AllCharacteristics.HomogeneousProjective
open AlgebraicGeometry

universe u v
set_option backward.isDefEq.respectTransparency false

def cubicFullJetCoordinates
    {K : Type u} [Field K] (x : Fin 11 → Fin 4 → K)
    (v : Fin 3 → Fin 4 → Fin 2 → K) : Fin 3 → Fin 4 → CubicSurfaceFirstJet K :=
  fun i j => TrivSqZeroExt.inl (x (i.castAdd 8) j) + TrivSqZeroExt.inr (v i j)

theorem cubicElevenPointHermiteRestriction_surjective_of_unitMinor
    {K : Type u} [Field K]
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
    (hm : IsUnit (homogeneousFullJetEvaluationMinor m x (fun i j => (J i j).snd)).det) :
    Function.Surjective (cubicElevenPointHermiteRestriction x J) := by
  classical
  have hM : IsUnit (homogeneousFullJetEvaluationMinor m x (fun i j => (J i j).snd)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hm
  intro z
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hM z
  let b : CubicFullJetCondition → homogeneousSubmodule (Fin 4) K 3 :=
    fun r => ⟨monomial (m r).1 1, isHomogeneous_monomial 1 (m r).2⟩
  let q : homogeneousSubmodule (Fin 4) K 3 := ∑ r, c r • b r
  refine ⟨q, ?_⟩
  funext r
  have h := congrFun hc r
  simpa [q, b, map_sum, map_smul, Matrix.mulVec, dotProduct,
    homogeneousFullJetEvaluationMinor,
    homogeneousFullJetEvaluationMatrix_entry_eq_restriction x J hresidue,
    smul_eq_mul, mul_comm] using h

theorem cubicElevenPointFullJetRestriction_surjective_of_hermite
    {K : Type u} [Field K]
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (hhermite : Function.Surjective (cubicElevenPointHermiteRestriction x J)) :
    Function.Surjective (cubicElevenPointFullJetRestriction x J) := by
  intro z
  let values : Fin 11 → K := fun i => Fin.addCases (m := 3) (n := 8)
    (fun j => (z.1 j).fst) z.2 i
  let w : CubicFullJetCondition → K := Sum.elim values (fun it => (z.1 it.1).snd it.2)
  obtain ⟨q, hq⟩ := hhermite w
  refine ⟨q, ?_⟩
  apply Prod.ext
  · funext i
    apply TrivSqZeroExt.ext
    · have h := congrFun hq (Sum.inl (i.castAdd 8))
      change aeval (x (i.castAdd 8)) q.1 = values (i.castAdd 8) at h
      change (aeval (J i) q.1).fst = (z.1 i).fst
      rw [cubicSurfaceFirstJet_fst_aeval]
      simpa [values, hresidue] using h
    · funext t
      have h := congrFun hq (Sum.inr (i, t))
      exact h
  · funext i
    have h := congrFun hq (Sum.inl (i.natAdd 3))
    change aeval (x (i.natAdd 3)) q.1 = values (i.natAdd 3) at h
    change aeval (x (i.natAdd 3)) q.1 = z.2 i
    simpa [values] using h

theorem cubicFullJetCoordinates_interpolation_of_unitMinor
    {K : Type u} [Field K] (x : Fin 11 → Fin 4 → K)
    (v : Fin 3 → Fin 4 → Fin 2 → K)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
    (hm : IsUnit (homogeneousFullJetEvaluationMinor m x v).det) :
    Function.Surjective
      (cubicElevenPointFullJetRestriction x (cubicFullJetCoordinates x v)) := by
  have hresidue : ∀ i j, (cubicFullJetCoordinates x v i j).fst = x (i.castAdd 8) j := by
    intros
    simp [cubicFullJetCoordinates]
  have hminor : IsUnit (homogeneousFullJetEvaluationMinor m x
      (fun i j => (cubicFullJetCoordinates x v i j).snd)).det := by
    simpa [cubicFullJetCoordinates] using hm
  exact cubicElevenPointFullJetRestriction_surjective_of_hermite x
    (cubicFullJetCoordinates x v) hresidue
    (cubicElevenPointHermiteRestriction_surjective_of_unitMinor x
      (cubicFullJetCoordinates x v) hresidue m hminor)

theorem cubicFullJetCoordinates_interpolation_on_minorOpen_fieldPoint
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (x : Fin 11 → Fin 4 → R) (v : Fin 3 → Fin 4 → Fin 2 → R)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
    (g : Localization.Away (homogeneousFullJetMinorDet m x v) →+* F) :
    let S := Localization.Away (homogeneousFullJetMinorDet m x v)
    let xF : Fin 11 → Fin 4 → F := fun i j => g (algebraMap R S (x i j))
    let vF : Fin 3 → Fin 4 → Fin 2 → F := fun i j t => g (algebraMap R S (v i j t))
    Function.Surjective (cubicElevenPointFullJetRestriction xF (cubicFullJetCoordinates xF vF)) := by
  let S := Localization.Away (homogeneousFullJetMinorDet m x v)
  let xS : Fin 11 → Fin 4 → S := fun i j => algebraMap R S (x i j)
  let vS : Fin 3 → Fin 4 → Fin 2 → S := fun i j t => algebraMap R S (v i j t)
  have hS : IsUnit (homogeneousFullJetEvaluationMinor m xS vS).det := by
    rw [← homogeneousFullJetEvaluationMinor_map]
    exact homogeneousFullJetMinor_isUnit_on_principalOpen m x v
  have hF := hS.map g
  rw [RingHom.map_det, RingHom.mapMatrix_apply, homogeneousFullJetEvaluationMinor_map] at hF
  exact cubicFullJetCoordinates_interpolation_of_unitMinor
    (fun i j => g (xS i j)) (fun i j t => g (vS i j t)) m hF

/-- An actual smooth cubic internally produces the nonzero full-jet
monomial minor needed to open the interpolation locus. -/
theorem exists_cubicSurfaceElevenPoint_native_unitJetMinor
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
      (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3),
      (∀ i, x i ≠ 0) ∧ (∀ i, aeval (x i) p = 0) ∧
      (∀ i j, i ≠ j → ∀ a : K, a • x i ≠ x j) ∧
      (∀ i j, (J i j).fst = x (i.castAdd 8) j) ∧
      (∀ i, aeval (J i) p = 0) ∧
      IsUnit (homogeneousFullJetEvaluationMinor m x (fun i j => (J i j).snd)).det := by
  obtain ⟨x, J, hx, hpx, hdir, hresidue, hpJ, hfull, _, _⟩ :=
    exists_cubicSurfaceElevenPoint_native_fullJet_witness p hp hp0
  obtain ⟨m, hm⟩ := exists_unit_homogeneousFullJetEvaluationMinor_of_fullJets x J hresidue hfull
  exact ⟨x, J, m, hx, hpx, hdir, hresidue, hpJ, hm⟩

end PfaffianDescent
