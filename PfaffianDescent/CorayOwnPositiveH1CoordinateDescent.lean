import PfaffianDescent.CorayOwnPositiveCoordinateCokernelHZero
import PfaffianDescent.ActualAmbientPositiveTwistQuotientIso
import PfaffianDescent.FiniteFiveTermLinearRank
import Mathlib.Data.Nat.Init

/-! SOURCE ONLY / UNCHECKED. Positive-to-zero H1 descent, conditional ONLY
on the natural eventual vanishing of actual ambient-pullback coefficients.
Root must internally construct this vanishing before any completed own H1
claim. Original coefficient/action maps, actual quotients and boundary maps
are retained. This file does not claim normalization finiteness or genus. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual coefficient iso transports native Ext linearly under the
SAME original pi action. Its value is actual covariant Ext postcomposition. -/
def ownCoordinateCohomologyIsoLinearEquiv
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    schemeModuleCohomology X M n ≃ₗ[K] schemeModuleCohomology X N n := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  refine { toAddEquiv := extPostcompIsoOfIso e, map_smul' := ?_ }
  intro c z
  change (c • z).comp (Ext.mk₀ e.hom) (add_zero n) =
    c • z.comp (Ext.mk₀ e.hom) (add_zero n)
  exact Ext.smul_comp z (Ext.mk₀ e.hom) (add_zero n) c

/-- The transported action comparison is literally the actual Ext map. -/
theorem ownCoordinateCohomologyIsoLinearEquiv_apply
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (e : M ≅ N) (n : ℕ)
    (z : schemeModuleCohomology X M n) :
    ownCoordinateCohomologyIsoLinearEquiv pi e n z =
      schemeModuleCohomologyMap X e.hom n z := rfl

/-- The actual linear iso also retains every incoming coefficient map. -/
theorem ownCoordinateCohomologyIsoLinearEquiv_map
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) {A M N : X.Modules}
    (e : M ≅ N) (f : A ⟶ M) (n : ℕ) (z : schemeModuleCohomology X A n) :
    ownCoordinateCohomologyIsoLinearEquiv pi e n
      (schemeModuleCohomologyMap X f n z) =
        schemeModuleCohomologyMap X (f ≫ e.hom) n z := by
  change (z.comp (Ext.mk₀ f) (add_zero n)).comp
    (Ext.mk₀ e.hom) (add_zero n) = z.comp (Ext.mk₀ (f ≫ e.hom)) (add_zero n)
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

/-- Actual ambient-pullback coefficient multiplication is defined by the
canonical actual graded quotient iso and the literal native coordinate map.
This definition does not assert it equals an independently encoded ambient
pullback morphism; the proved square below is the compatibility used here. -/
def ownAmbientPullbackCoordinateMultiplication
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    (Scheme.Modules.pullback (quotientProjMap C)).obj
      (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m) ⟶
    (Scheme.Modules.pullback (quotientProjMap C)).obj
      (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) (m + 1)) :=
  (actualAmbientPositiveTwistQuotientIso C m).hom ≫
    ownPositiveCoordinateMultiplication C j m ≫
      (actualAmbientPositiveTwistQuotientIso C (m + 1)).inv

private theorem coordinateIsoConjugationSquare
    {D : Type*} [Category D] {A B C E : D}
    (e : A ≅ B) (f : B ⟶ C) (d : E ≅ C) :
    (e.hom ≫ f ≫ d.inv) ≫ d.hom = e.hom ≫ f := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Both coefficients and the multiplication square are actual; no map
compatibility is supplied to the descent. -/
theorem ownAmbientPullbackCoordinateMultiplication_square
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    ownAmbientPullbackCoordinateMultiplication C j m ≫
      (actualAmbientPositiveTwistQuotientIso C (m + 1)).hom =
    (actualAmbientPositiveTwistQuotientIso C m).hom ≫
      ownPositiveCoordinateMultiplication C j m := by
  exact coordinateIsoConjugationSquare (actualAmbientPositiveTwistQuotientIso C m)
    (ownPositiveCoordinateMultiplication C j m)
    (actualAmbientPositiveTwistQuotientIso C (m + 1))

/-- Minimal backward finite-H1 step uses actual original-pi linear boundary
and inclusion. Finite H0 of the middle coefficient is unnecessary. -/
theorem ownCoordinate_shortExact_finite_h1_first
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) →
    Module.Finite K (schemeModuleCohomology X S.X₂ 1) →
    Module.Finite K (schemeModuleCohomology X S.X₁ 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hQ hN
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) := hQ
  letI : Module.Finite K (schemeModuleCohomology X S.X₂ 1) := hN
  exact moduleFinite_middle_of_exact
    (schemeModuleOpenTopConnectingLinearMapOver pi S hS)
    (schemeModuleCohomologyLinearMapOver pi S.f 1)
    (schemeModuleOpenTopConnectingLinearMaps_exact pi S hS).2

/-- Conditional natural helper endpoint: genuine selected geometry,
SAME-P coordinate choice, actual positive sequences/finite quotient H0 and
original-pi Ext actions derive finite unit H1 from eventual positive H1
vanishing on SAME actual ambient-pullback coefficients. The only supplied
cohomological input is exactly the scalar producer's intended interface. -/
theorem selectedProjectivePrimeComponent_unitH1_finite_of_eventually_ownPositivePullback_vanishes
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) [hExtC : HasExt.{u} (scheme C).Modules]
    (hvanish : ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Subsingleton (schemeModuleCohomology.{u} (scheme C)
        ((Scheme.Modules.pullback (quotientProjMap C)).obj
          (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m)) 1)) :
    letI : HasExt.{u} (SheafOfModules.{u} (scheme C).ringCatSheaf) := hExtC
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    Module.Finite K (schemeModuleCohomology.{u} (scheme C)
      (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} (scheme C).ringCatSheaf) := hExtC
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  obtain ⟨j, hj⟩ := projectivePoint_exists_coordinate_notMem C P
  obtain ⟨B, hB⟩ := hvanish
  let T (m : ℕ) : (scheme C).Modules := positiveSheafOfModules (grading C) m
  have hstart : Module.Finite K (schemeModuleCohomology.{u} (scheme C) (T B) 1) := by
    letI : Subsingleton (schemeModuleCohomology.{u} (scheme C)
      ((Scheme.Modules.pullback (quotientProjMap C)).obj
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) B)) 1) :=
      hB B le_rfl
    letI : Subsingleton (schemeModuleCohomology.{u} (scheme C) (T B) 1) :=
      schemeModuleCohomology_subsingleton_of_iso (scheme C)
        (actualAmbientPositiveTwistQuotientIso C B) 1
    infer_instance
  have hstep (m : ℕ) (_hm : m < B)
      (hm : Module.Finite K (schemeModuleCohomology.{u} (scheme C) (T (m + 1)) 1)) :
      Module.Finite K (schemeModuleCohomology.{u} (scheme C) (T m) 1) := by
    let S : ShortComplex (scheme C).Modules :=
      ShortComplex.cokernelSequence (ownPositiveCoordinateMultiplication C j m)
    have hS : S.ShortExact :=
      ownPositiveCoordinateMultiplication_cokernelSequence_shortExact C hprime P j hj m
    exact ownCoordinate_shortExact_finite_h1_first (toBase C) S hS
      (selectedProjectivePrimeComponent_ownPositiveCoordinateCokernel_topSections_finite
        p q hp hp0 n hq hnot C hIC hprime P j hj m) hm
  have hzero : Module.Finite K (schemeModuleCohomology.{u} (scheme C) (T 0) 1) :=
    Nat.decreasingInduction (motive := fun m _ =>
      Module.Finite K (schemeModuleCohomology.{u} (scheme C) (T m) 1))
      hstep hstart (Nat.zero_le B)
  letI : Module.Finite K (schemeModuleCohomology.{u} (scheme C) (T 0) 1) := hzero
  let e : T 0 ≅ (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) :=
    positiveZeroTwistIso (grading C) ≪≫ (unitIsoZeroTwist (grading C)).symm
  exact Module.Finite.equiv (ownCoordinateCohomologyIsoLinearEquiv (toBase C) e 1)

end PfaffianDescent.Coray
