import PfaffianDescent.QuarticSkewTangentConstruction
import PfaffianDescent.QuarticGeometricNetAssembly
import PfaffianDescent.QuarticHomogeneousJets

/-!
# Assembly from a degree-four affine point

This connects the trace-selected length-eight tangent construction to the
finite and matching branches of the Section 4 tangent-net argument.  Starting
with a smooth affine chart of a degree-four point, the only alternative left
is the full-support exceptional discriminant locus.
-/

namespace PfaffianDescent
namespace QuarticNet

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module

universe u

/-- From a smooth affine degree-four point with independent homogeneous
coordinates, the tangent-net argument gives a ground-field cubic point unless
the normalized full-support matrix is on the exceptional discriminant locus. -/
theorem affine_cubic_point_or_exceptional_tangent_net
    {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [IsAlgClosed K] [Normal k K] [Infinite K] [IsGalois k K]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hp : MvPolynomial.aeval b F = 0)
    (hsmooth : affineDifferential (fun i : Fin 3 => b i.succ)
      (dehomogenizeAtZero F) ≠ 0) :
    (∃ x : Fin 4 → k, x ≠ 0 ∧ MvPolynomial.aeval x F = 0) ∨
      (∃ (e : Fin 4 ≃ (L →ₐ[k] K)) (v : Fin 3 → L) (l : Fin 4 → K),
        (∀ i, l i ≠ 0) ∧
        (∀ i j, i ≠ j →
          rescaleTangentDirections l
            (conjugateTangentMatrix e b (Fin.cons 0 v) (conjugate_basis_span b e)) i j ≠ 0) ∧
        baseLocusDelta
          (rescaleTangentDirections l
            (conjugateTangentMatrix e b (Fin.cons 0 v) (conjugate_basis_span b e)) 0 1)
          (rescaleTangentDirections l
            (conjugateTangentMatrix e b (Fin.cons 0 v) (conjugate_basis_span b e)) 0 2)
          (rescaleTangentDirections l
            (conjugateTangentMatrix e b (Fin.cons 0 v) (conjugate_basis_span b e)) 0 3)
          (rescaleTangentDirections l
            (conjugateTangentMatrix e b (Fin.cons 0 v) (conjugate_basis_span b e)) 1 2)
          (rescaleTangentDirections l
            (conjugateTangentMatrix e b (Fin.cons 0 v) (conjugate_basis_span b e)) 1 3)
          (rescaleTangentDirections l
            (conjugateTangentMatrix e b (Fin.cons 0 v) (conjugate_basis_span b e)) 2 3) = 0) := by
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
  obtain ⟨e, v, hjet, hv, -, -, -, hdim, l, hl, hskew⟩ :=
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
    e b (Fin.cons (0 : L) v) hb (by rfl) hv' (conjugate_basis_span b e) hdim' l hl hskew F hF hhomjet
  · exact Or.inl hpoint
  · obtain ⟨hfull, hdelta⟩ := hexception
    exact Or.inr ⟨e, v, l, hl, hfull, hdelta⟩

end QuarticNet
end PfaffianDescent
