import PfaffianDescent.QuarticAffineTangentSelection
import PfaffianDescent.QuarticGeometricSplitting

/-!
# Geometrically split affine length-eight construction

This packages the affine part of Proposition 4.3: the selected embedded
dual-number point has ground-field length eight and becomes four length-two
points after an algebraically closed base change.
-/

namespace PfaffianDescent
namespace QuarticNet

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module

universe u

theorem affine_length_eight_construction_geometrically_split
    {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1) (F : AffineThreeRing k)
    (hp : MvPolynomial.aeval (fun i : Fin 3 => b i.succ) F = 0)
    (hsmooth : affineDifferential (fun i : Fin 3 => b i.succ) F ≠ 0) :
    ∃ v : Fin 3 → L, ∃ hF : affineFirstJet (fun i : Fin 3 => b i.succ) v F = 0,
      v ≠ 0 ∧
      Function.Surjective (affineHypersurfaceJet (fun i : Fin 3 => b i.succ) v F hF) ∧
      IsClosedImmersion
        (Spec.map (CommRingCat.ofHom
          (affineHypersurfaceJet (fun i : Fin 3 => b i.succ) v F hF).toRingHom)) ∧
      Module.finrank k (DualNumber L) = 8 ∧
      3 ≤ Module.finrank k (affineJetQuadrics (k := k) (fun i : Fin 3 => b i.succ) v) ∧
      ∃ (I : Type u) (_ : Fintype I), Fintype.card I = 4 ∧
        Nonempty (pullback
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber L)))) ≅
          ∐ fun _ : I => Spec (.of (DualNumber K))) := by
  obtain ⟨v, hjet, hv, hsurj, hclosed, hdim, hquad⟩ :=
    affine_length_eight_construction b hb F hp hsmooth
  have hL : Module.finrank k L = 4 := by simpa using finrank_eq_card_basis b
  obtain ⟨I, hI, hcard, hsplit⟩ := degree_four_dualPoint_scheme_splits k K L hL
  exact ⟨v, hjet, hv, hsurj, hclosed, hdim, hquad, I, hI, hcard, hsplit⟩

end QuarticNet
end PfaffianDescent
