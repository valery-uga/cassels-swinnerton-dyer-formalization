import PfaffianDescent.CorayNormalizationClosedPointIdealRankOne
import PfaffianDescent.SchemeModuleBaseLinearCategory
import Mathlib.LinearAlgebra.Contraction

/-! Genuine local dual and canonical evaluation of the ACTUAL affine
point-ideal sections. This is a local tensor inverse over the ORIGINAL
affine ring, not a constructed global positive pole sheaf. Gluing the dual
as a module sheaf and its global evaluation are explicitly still missing.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- For a genuine rank-one module, the CANONICAL dual evaluation is a
linear equivalence. Its map is the installed contractRight, independent
of the choice of rank-one generator; the generator only constructs its
inverse. Natural algebraic intermediate, discharged by the point charts. -/
def rankOneCanonicalDualTensorEquiv
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (e : R ≃ₗ[R] M) : M ⊗[R] Module.Dual R M ≃ₗ[R] R := by
  let d : Module.Dual R M := e.symm.toLinearMap
  let inv : R →ₗ[R] M ⊗[R] Module.Dual R M :=
    ((TensorProduct.mk R M (Module.Dual R M)).flip d).comp e.toLinearMap
  apply LinearEquiv.ofLinearMap (contractRight R M) inv
  · apply LinearMap.ext
    intro r
    change e.symm (e r) = r
    exact e.symm_apply_apply r
  · apply TensorProduct.ext'
    intro x f
    change e (f x) ⊗ₜ[R] d = x ⊗ₜ[R] f
    have hf : f = f (e 1) • d := by
      apply LinearMap.ext
      intro y
      change f y = f (e 1) * e.symm y
      calc
        f y = f (e (e.symm y • (1 : R))) := by
          rw [smul_eq_mul, mul_one, e.apply_symm_apply]
        _ = e.symm y • f (e 1) := by rw [e.map_smul, f.map_smul]
        _ = f (e 1) * e.symm y := by rw [smul_eq_mul, mul_comm]
    rw [hf]
    change e (f (e 1) • e.symm x) ⊗ₜ[R] d = x ⊗ₜ[R] (f (e 1) • d)
    rw [e.map_smul, e.apply_symm_apply]
    exact TensorProduct.smul_tmul (f (e 1)) x d

/-- The map above is literal evaluation, not a generator-dependent
replacement pairing. -/
theorem rankOneCanonicalDualTensorEquiv_apply
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (e : R ≃ₗ[R] M) (m : M) (f : Module.Dual R M) :
    rankOneCanonicalDualTensorEquiv e (m ⊗ₜ[R] f) = f m := rfl

/-- Canonical dual evaluation for the SAME actual ideal-module sections
on a genuinely regular-principal affine open. Actual ring-linear dual,
actual tensor product and original local-ring action are retained. -/
def closedImmersionModule_affineDualTensorEquiv
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (z : Γ(X, U.1)) (hz : IsRegular z)
    (hprincipal : i.ker.ideal U = Ideal.span ({z} : Set Γ(X, U.1))) :
    let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    letI : Module (Γ(X, U.1)) (M.val.presheaf.obj (op U.1)) := by
      change Module ((X.ringCatSheaf.obj).obj (op U.1)) (M.val.presheaf.obj (op U.1))
      infer_instance
    M.val.presheaf.obj (op U.1) ⊗[Γ(X, U.1)]
      Module.Dual (Γ(X, U.1)) (M.val.presheaf.obj (op U.1)) ≃ₗ[Γ(X, U.1)] Γ(X, U.1) := by
  let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
  letI : Module (Γ(X, U.1)) (M.val.presheaf.obj (op U.1)) := by
    change Module ((X.ringCatSheaf.obj).obj (op U.1)) (M.val.presheaf.obj (op U.1))
    infer_instance
  exact rankOneCanonicalDualTensorEquiv
    (closedImmersionModule_affineSectionsLinearEquivPrincipal i U z hz hprincipal)

/-- The SAME affine evaluation sends m tensor f to f(m). -/
theorem closedImmersionModule_affineDualTensorEquiv_apply
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (z : Γ(X, U.1)) (hz : IsRegular z)
    (hprincipal : i.ker.ideal U = Ideal.span ({z} : Set Γ(X, U.1))) :
    let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    letI : Module (Γ(X, U.1)) (M.val.presheaf.obj (op U.1)) := by
      change Module ((X.ringCatSheaf.obj).obj (op U.1)) (M.val.presheaf.obj (op U.1))
      infer_instance
    ∀ (m : M.val.presheaf.obj (op U.1))
      (f : Module.Dual (Γ(X, U.1)) (M.val.presheaf.obj (op U.1))),
      closedImmersionModule_affineDualTensorEquiv i U z hz hprincipal
        (m ⊗ₜ[Γ(X, U.1)] f) = f m := by
  dsimp only
  intro m f
  rfl

variable {K : Type u} [Field K]

/-- Literal original pi-induced constants commute with the SAME canonical
affine evaluation. The scalar is the ACTUAL schemeOpenBaseRingHom pi U c;
no intrinsic action is transported to force this compatibility. -/
theorem closedImmersionModule_affineDualTensorEquiv_originalBaseConstant
    {X Z : Scheme.{u}} (pi : X ⟶ Spec (CommRingCat.of K))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (z : Γ(X, U.1)) (hz : IsRegular z)
    (hprincipal : i.ker.ideal U = Ideal.span ({z} : Set Γ(X, U.1))) :
    let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    letI : Module (Γ(X, U.1)) (M.val.presheaf.obj (op U.1)) := by
      change Module ((X.ringCatSheaf.obj).obj (op U.1)) (M.val.presheaf.obj (op U.1))
      infer_instance
    ∀ (c : K) (m : M.val.presheaf.obj (op U.1))
      (f : Module.Dual (Γ(X, U.1)) (M.val.presheaf.obj (op U.1))),
      closedImmersionModule_affineDualTensorEquiv i U z hz hprincipal
        ((schemeOpenBaseRingHom pi U.1 c • m) ⊗ₜ[Γ(X, U.1)] f) =
          schemeOpenBaseRingHom pi U.1 c * f m := by
  let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
  letI : Module (Γ(X, U.1)) (M.val.presheaf.obj (op U.1)) := by
    change Module ((X.ringCatSheaf.obj).obj (op U.1)) (M.val.presheaf.obj (op U.1))
    infer_instance
  dsimp only
  intro c m f
  rw [closedImmersionModule_affineDualTensorEquiv_apply]
  exact f.map_smul (schemeOpenBaseRingHom pi U.1 c) m

/-- Build the genuine canonical local dual evaluation from an actual
point-ideal chart, before substituting the normalization construction. -/
private theorem closedPointIdeal_localDualTensorInverse_of_chart
    (N : Scheme.{u}) (P : closedPoints N) (x : N)
    (hchart :
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
      ∃ U : N.affineOpens, x ∈ U.1 ∧ ∃ m : M.val.presheaf.obj (op U.1),
        IsIso (schemeModuleSectionOnOpenHom M U.1 m) ∧
        let z : Γ(N, U.1) :=
          (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m
        IsRegular z ∧ i.ker.ideal U = Ideal.span ({z} : Set Γ(N, U.1))) :
    let i := N.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
    ∃ U : N.affineOpens, x ∈ U.1 ∧
      letI : Module (Γ(N, U.1)) (M.val.presheaf.obj (op U.1)) := by
        change Module ((N.ringCatSheaf.obj).obj (op U.1)) (M.val.presheaf.obj (op U.1))
        infer_instance
      ∃ E : M.val.presheaf.obj (op U.1) ⊗[Γ(N, U.1)]
        Module.Dual (Γ(N, U.1)) (M.val.presheaf.obj (op U.1)) ≃ₗ[Γ(N, U.1)] Γ(N, U.1),
        ∀ m f, E (m ⊗ₜ[Γ(N, U.1)] f) = f m := by
  dsimp only at hchart ⊢
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨U, hxU, m, _hiso, hz, hprincipal⟩ := hchart
  let z : Γ(N, U.1) :=
    (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m
  refine ⟨U, hxU, closedImmersionModule_affineDualTensorEquiv i U z hz hprincipal, ?_⟩
  intro m f
  exact closedImmersionModule_affineDualTensorEquiv_apply i U z hz hprincipal m f

variable [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every point of the SAME normalization admits the genuine local dual
tensor inverse of the SAME point ideal's actual affine sections. Geometry,
regular generator and rank-one equivalence are all derived internally.
This is explicitly LOCAL; no global dual/pole sheaf is asserted. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_localDualTensorInverse
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ (P : closedPoints N) (x : N),
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
      ∃ U : N.affineOpens, x ∈ U.1 ∧
        letI : Module (Γ(N, U.1)) (M.val.presheaf.obj (op U.1)) := by
          change Module ((N.ringCatSheaf.obj).obj (op U.1)) (M.val.presheaf.obj (op U.1))
          infer_instance
        ∃ E : M.val.presheaf.obj (op U.1) ⊗[Γ(N, U.1)]
          Module.Dual (Γ(N, U.1)) (M.val.presheaf.obj (op U.1)) ≃ₗ[Γ(N, U.1)] Γ(N, U.1),
          ∀ m f, E (m ⊗ₜ[Γ(N, U.1)] f) = f m := by
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P x
  exact closedPointIdeal_localDualTensorInverse_of_chart N P x
    (projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
      p q hp hp0 n hn hq hnot P x)

end PfaffianDescent.Coray
