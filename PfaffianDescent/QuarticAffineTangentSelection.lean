import PfaffianDescent.QuarticAffineQuadrics
import PfaffianDescent.QuarticTraceQuotient

/-!
# Selecting the length-eight tangent subscheme

This is the affine, coordinate-level form of Proposition 4.3.  From a
separable degree-four point of a smooth cubic whose coordinates span the
residue field, it produces an embedded dual-number point of ground-field
dimension eight and at least three independent quadrics vanishing on it.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module AlgebraicGeometry

universe u

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Restrict the differential of a quadric to the tangent space of the
affine cubic at the degree-four point. -/
noncomputable def affineQuadricCotangentRestriction (p : Fin 3 → L)
    (F : AffineThreeRing k) :
    affineQuadricsThroughPoint (k := k) p →ₗ[k]
      Module.Dual L (LinearMap.ker (affineDifferential p F)) :=
  (((LinearMap.domRestrict' (LinearMap.ker (affineDifferential p F))).restrictScalars k).comp
    ((affineDifferentialMap p).comp affineQuadrics)).domRestrict (affineQuadricsThroughPoint p)

/-- The subspace of affine quadrics which vanish on the dual point defined
by `(p,v)`. -/
noncomputable def affineJetQuadrics (p v : Fin 3 → L) : Submodule k (Fin 10 → k) :=
  LinearMap.ker ((affineFirstJet p v).toLinearMap.comp affineQuadrics)

/-- A tangent direction selected by trace duality has at least three affine
quadrics vanishing on its dual point. -/
theorem good_affine_tangent_direction [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1) (F : AffineThreeRing k)
    (hF : affineDifferential (fun i : Fin 3 => b i.succ) F ≠ 0) :
    ∃ v : Fin 3 → L, v ≠ 0 ∧
      affineDifferential (fun i : Fin 3 => b i.succ) F v = 0 ∧
      3 ≤ Module.finrank k (affineJetQuadrics (k := k) (fun i : Fin 3 => b i.succ) v) := by
  let p : Fin 3 → L := fun i => b i.succ
  let T := LinearMap.ker (affineDifferential p F)
  let E := Module.Dual L T
  let φ := affineQuadricCotangentRestriction p F
  have hL : Module.finrank k L = 4 := by simpa using finrank_eq_card_basis b
  have hE : Module.finrank L E = 2 := by
    rw [Subspace.dual_finrank_eq]
    exact affineTangentSpace_finrank p F hF
  obtain ⟨q, hq, _, hdim⟩ := quotient_with_large_kernel φ hL hE
    (affineQuadricsThroughPoint_finrank b hb)
  let v : T := (Module.evalEquiv L T).symm q
  have hv : v ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := hq 1
    have he : x v = q x := Module.apply_evalEquiv_symm_apply L T x q
    rw [hz, map_zero, hx] at he
    exact zero_ne_one he
  refine ⟨v.val, ?_, v.property, ?_⟩
  · intro hz
    exact hv (Subtype.ext hz)
  · let g : affineQuadricsThroughPoint (k := k) p →ₗ[k] L :=
      (q.restrictScalars k).comp φ
    let inclusion : LinearMap.ker g →ₗ[k] affineJetQuadrics (k := k) p v.val :=
      { toFun x := ⟨x.val.val, by
          apply (affineFirstJet_eq_zero_iff p v.val (affineQuadrics x.val.val)).mpr
          constructor
          · exact x.val.property
          · have he : (φ x.val) v = q (φ x.val) :=
              Module.apply_evalEquiv_symm_apply L T (φ x.val) q
            exact he.trans x.property⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    have hinj : Function.Injective inclusion := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : affineJetQuadrics (k := k) p v.val => z.val) hxy
    exact hdim.trans (LinearMap.finrank_le_finrank_of_injective hinj)

/-- The complete affine realization of the length-eight construction. -/
theorem affine_length_eight_construction [FiniteDimensional k L] [Algebra.IsSeparable k L]
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
      3 ≤ Module.finrank k (affineJetQuadrics (k := k) (fun i : Fin 3 => b i.succ) v) := by
  obtain ⟨v, hv, ht, hquad⟩ := good_affine_tangent_direction b hb F hsmooth
  have hjet := (affineFirstJet_eq_zero_iff (fun i : Fin 3 => b i.succ) v F).mpr ⟨hp, ht⟩
  refine ⟨v, hjet, hv,
    affineHypersurfaceJet_surjective _ _ _ (affineResidueEvaluation_surjective b hb) hv hjet,
    affineHypersurfaceJet_closedImmersion _ _ _ (affineResidueEvaluation_surjective b hb) hv hjet,
    ?_, hquad⟩
  have hL : Module.finrank k L = 4 := by simpa using finrank_eq_card_basis b
  change Module.finrank k (L × L) = 8
  simp [Module.finrank_prod, hL]

end QuarticNet
end PfaffianDescent
