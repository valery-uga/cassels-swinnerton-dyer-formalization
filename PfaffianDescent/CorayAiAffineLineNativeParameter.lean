import PfaffianDescent.CorayAiDominantPencilAttainedOpen

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every rational section of the universe-correct native affine line is
the SAME original-K evaluation at an actual parameter t. -/
theorem affineLine_rationalSection_eq_native_parameter001
    {K : Type u} [Field K]
    (q : Spec (.of K) ⟶ AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)))
    (hq : q ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) ↘ Spec (.of K)) = 𝟙 _) :
    ∃ t : K, q = Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : ULift.{u} (Fin 1) => t))) ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)).inv := by
  let E := AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of K)
  let q' := q ≫ E.hom
  let psi : MvPolynomial (ULift.{u} (Fin 1)) K →+* K := (Spec.preimage q').hom
  have hSpec : Spec.map (CommRingCat.ofHom psi) = q' := Spec.map_preimage q'
  have hOver : Spec.map (CommRingCat.ofHom psi) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin 1)) K)) =
      𝟙 (Spec (.of K)) := by
    calc
      _ = (q ≫ E.hom) ≫
          (E.inv ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) ↘ Spec (.of K))) := by
        rw [hSpec, AffineSpace.SpecIso_inv_over]
      _ = q ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of K)) ↘ Spec (.of K)) := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = _ := hq
  have hSpecCoeff : Spec.map (CommRingCat.ofHom (psi.comp MvPolynomial.C)) = 𝟙 _ := by
    change Spec.map ((CommRingCat.ofHom
      (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin 1)) K)) ≫
        CommRingCat.ofHom psi) = 𝟙 _
    rw [Spec.map_comp]
    exact hOver
  have hCoeff : psi.comp MvPolynomial.C = RingHom.id K := by
    have hm := Spec.map_eq_id.mp hSpecCoeff
    exact congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of K => h.hom) hm
  let t : K := psi (MvPolynomial.X default)
  have hPsi : psi = MvPolynomial.eval₂Hom (RingHom.id K)
      (fun _ : ULift.{u} (Fin 1) => t) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.id_apply]
      exact RingHom.congr_fun hCoeff c
    · intro i
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [Unique.eq_default i]
  refine ⟨t, ?_⟩
  rw [← hPsi, hSpec]
  dsimp only [q']
  change q = (q ≫ E.hom) ≫ E.inv
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end PfaffianDescent.Coray
