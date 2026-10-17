import PfaffianDescent.QuarticCoordinateChangedJetIdeal
import PfaffianDescent.QuarticGeometricNetAssembly
import PfaffianDescent.QuarticSkewTangentConstruction
import PfaffianDescent.ProjectiveDescent

/-!
# The full exceptional ground-jet branch

This joins the ground-field tangent jet, its exceptional three-quadric net,
and the descended rank-nine intersection.  If the transformed cubic contains
the exceptional curve, ideal descent gives a point directly; otherwise the
rank-eight jet has a degree-one residual in the finite rank-nine intersection.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Infinite K]

/-- The full-support exceptional branch for a normalized ground tangent jet
produces a rational section of the cubic. -/
theorem cubic_section_of_exceptional_full_support_ground_jet
    {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0) (hv : v ≠ 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (hsurj : Function.Surjective (MvPolynomial.aeval
      (fun i : Fin 3 => p i.succ) : AffineThreeRing k →ₐ[k] L))
    (hrank : Module.finrank k (DualNumber L) = 8)
    (l : Fin 4 → K)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hfull : ∀ i j, i ≠ j →
      rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j ≠ 0)
    (hdelta : baseLocusDelta
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 1)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 0 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 2)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 1 3)
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) 2 3) = 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : MvPolynomial.aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  let M := basisCoordinateMatrix (conjugateBasis e p hspan)
  let U := rescaleTangentDirections l (conjugateTangentMatrix e p v hspan)
  have hM : IsUnit M.det := basisCoordinateMatrix_isUnit (conjugateBasis e p hspan)
  have hdiag : ∀ i, U i i = 0 := by
    intro i
    simp [U, rescaleTangentDirections, conjugateTangentMatrix_diagonal]
  have hskewU : ∀ i j, U i j = -U j i := by
    simpa only [U, rescaleTangentDirections] using hskew
  by_cases hcontained : exceptionalTwistedCubicParam
      (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3)
      (linearSubstitution M (map (algebraMap k K) F)) = 0
  · obtain ⟨x, hx, hFx⟩ := cubic_point_of_exceptional_ground_jet_of_mem_param
      e p v hp hv0 hspan hdim l hskew hfull (by simpa [U] using hdelta) F hF
      (by simpa [M] using hcontained)
    exact PfaffianDescent.cubic_projective_section_of_coordinates F hF x hx hFx
  · obtain ⟨Q, hQI, hQ, hQjet⟩ := exists_three_ground_quadrics p v hp hv0 hdim
    have hQideal : Ideal.span (Set.range (fun i =>
        linearSubstitution M (map (algebraMap k K) (Q i)))) =
        RingHom.ker (exceptionalTwistedCubicParam
          (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3)).toRingHom := by
      apply exceptional_ground_quadric_ideal_eq_param_ker Q hQ hQI
        (conjugateBasis e p hspan) U hdiag hskewU hfull
      · simpa [U] using hdelta
      · intro i r
        simpa only [U] using
          (rescaleTangentDirections_vanishing _ l _ (fun r =>
            (homogeneous_jet_vanishes_on_conjugates e p v hspan (Q i) 2
              (hQ i) (hQjet i)) r)) r
    have hvTail : (fun i : Fin 3 => v i.succ) ≠ 0 := by
      intro hzero
      apply hv
      funext i
      refine Fin.cases ?_ ?_ i
      · exact hv0
      · intro j
        exact congrFun hzero j
    have hQjet' : ∀ i, MvPolynomial.aeval
        (homogeneousAffineDualPoint (fun i : Fin 3 => p i.succ)
          (fun i : Fin 3 => v i.succ)) (Q i) = 0 := by
      intro i
      rw [homogeneousAffineDualPoint_eq_dual p v hp hv0]
      exact hQjet i
    have hFjet' : MvPolynomial.aeval
        (homogeneousAffineDualPoint (fun i : Fin 3 => p i.succ)
          (fun i : Fin 3 => v i.succ)) F = 0 := by
      rw [homogeneousAffineDualPoint_eq_dual p v hp hv0]
      exact hFjet
    obtain ⟨j, hj, hfinite, hjet, _⟩ :=
      homogeneousAffineJet_rank_eight_in_quadricCubicIntersection Q hQ F hF
        (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)
        hsurj hvTail hQjet' hFjet' hrank
    letI : IsClosedImmersion j := hj
    letI : IsFinite (j ≫ jetQuadricCubicIntersectionToHypersurface Q hQ F hF ≫
        hypersurfaceToBase F hF) := hfinite
    exact cubic_section_of_ground_exceptional_jet_intersection
      M hM Q hQ F hF (U 0 1) (U 0 2) (U 0 3) (U 1 2) (U 1 3) (U 2 3)
      (hfull 0 1 (by decide)) (hfull 0 2 (by decide))
      (hfull 0 3 (by decide)) (hfull 1 2 (by decide))
      (hfull 1 3 (by decide)) (by simpa [U] using hdelta)
      (by simpa [M] using hQideal) (by simpa [M] using hcontained) j hjet

/-- Starting with a smooth affine degree-four point, the tangent-net
construction now closes its exceptional full-support branch as well.  The
finite and matching branches are handled by the preceding case split, while
the remaining discriminant-zero branch is the rank-nine residual argument
above. -/
theorem cubic_section_of_smooth_affine_degree_four_point
    {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [IsAlgClosed K] [Normal k K] [IsGalois k K]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hp : MvPolynomial.aeval b F = 0)
    (hsmooth : affineDifferential (fun i : Fin 3 => b i.succ)
      (dehomogenizeAtZero F) ≠ 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  have hpaff : MvPolynomial.aeval (fun i : Fin 3 => b i.succ)
      (dehomogenizeAtZero F) = 0 := by
    have hcomp : (MvPolynomial.aeval (fun i : Fin 3 => b i.succ)).comp
        (dehomogenizeAtZero (k := k)) = MvPolynomial.aeval b := by
      ext i : 1
      fin_cases i <;> simp [dehomogenizeAtZero, hb]
    calc
      MvPolynomial.aeval (fun i : Fin 3 => b i.succ) (dehomogenizeAtZero F) =
          MvPolynomial.aeval b F := AlgHom.congr_fun hcomp F
      _ = 0 := hp
  obtain ⟨e, v, hjet, hv, -, -, hrank, hdim, l, hl, hskew⟩ :=
    affine_length_eight_skew_tangent_construction_with_quadric_dimension
      (K := K) b hb (dehomogenizeAtZero F) hpaff hsmooth
  have hv' : (Fin.cons (0 : L) v : Fin 4 → L) ≠ 0 := by
    intro hz
    apply hv
    funext i
    simpa using congrFun hz i.succ
  have hdim' : 3 ≤ Module.finrank k (affineJetQuadrics (k := k)
      (fun i : Fin 3 => b i.succ)
      (fun i : Fin 3 => (Fin.cons (0 : L) v : Fin 4 → L) i.succ)) := by
    have htail : (fun i : Fin 3 =>
        (Fin.cons (0 : L) v : Fin 4 → L) i.succ) = v := by
      funext i
      simp
    rw [htail]
    exact hdim
  have hhomjet : MvPolynomial.aeval
      (fun i => TrivSqZeroExt.inl (b i) + TrivSqZeroExt.inr
        ((Fin.cons (0 : L) v : Fin 4 → L) i)) F = 0 := by
    have h := homogeneousAffineDualPoint_vanishes_of_affineFirstJet
      (fun i : Fin 3 => b i.succ) v F hjet
    have heq : homogeneousAffineDualPoint (fun i : Fin 3 => b i.succ) v =
        fun i => TrivSqZeroExt.inl (b i) + TrivSqZeroExt.inr
          ((Fin.cons (0 : L) v : Fin 4 → L) i) := by
      funext i
      fin_cases i <;> simp [homogeneousAffineDualPoint, hb, Fin.cons] <;> rfl
    rw [← heq]
    exact h
  obtain hpoint | hexception := cubic_point_or_exceptional_full_support_ground_jet
    e b (Fin.cons (0 : L) v) hb (by rfl) hv'
      (conjugate_basis_span b e) hdim' l hl hskew F hF hhomjet
  · obtain ⟨x, hx, hFx⟩ := hpoint
    exact PfaffianDescent.cubic_projective_section_of_coordinates F hF x hx hFx
  · obtain ⟨hfull, hdelta⟩ := hexception
    exact cubic_section_of_exceptional_full_support_ground_jet
      e b (Fin.cons (0 : L) v) hb (by rfl) hv'
      (conjugate_basis_span b e) hdim'
      (affineResidueEvaluation_surjective b hb) hrank l hskew hfull hdelta F hF hhomjet

end QuarticNet
end PfaffianDescent
