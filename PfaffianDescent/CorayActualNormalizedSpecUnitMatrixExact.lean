import PfaffianDescent.CorayActualFinitePiTildeUnitMatrix
import PfaffianDescent.CorayActualDegreeZeroChartTildeExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Canonical tilde/unit comparison of the SAME normalized degree-zero chart
matrices. Exactness comes from the actual homogeneous presentation, not from
an assumed native matrix comparison. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The SAME normalized generator coefficients as actual Spec-unit maps. -/
def actualNormalizedSpecUnitGeneratorMatrix
    {ι : Type u} [Fintype ι] (j : Fin 4) (g : ι → A) :
    (∐ fun _ : ι => SheafOfModules.unit
      (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) ⟶
    SheafOfModules.unit
      (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf :=
  Sigma.desc (fun i => unitEndomorphismOfRegularFunction
    ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).inv.hom
      (ambientChartEvaluation j (g i))))

/-- The SAME normalized relation coefficients, including every matrix entry. -/
def actualNormalizedSpecUnitRelationMatrix
    {ι κ : Type u} [Fintype ι] [Fintype κ] (j : Fin 4) (r : κ → ι → A) :
    (∐ fun _ : κ => SheafOfModules.unit
      (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) ⟶
    (∐ fun _ : ι => SheafOfModules.unit
      (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) :=
  Sigma.desc (fun a => ∑ i, unitEndomorphismOfRegularFunction
    ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).inv.hom
      (ambientChartEvaluation j (r a i))) ≫ Sigma.ι
        (fun _ : ι => SheafOfModules.unit
          (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).ringCatSheaf) i)

private theorem actualChartGenerator_injection
    {ι : Type u} [Fintype ι] (j : Fin 4) (g : ι → A) (i : ι) :
    actualFinitePiInjection (HomogeneousLocalization.Away PS (X j)) ι i ≫
      ModuleCat.ofHom (actualDegreeZeroChartGeneratorMap j g) =
    ModuleCat.ofHom (actualRingMultiplicationMap
      (HomogeneousLocalization.Away PS (X j)) (ambientChartEvaluation j (g i))) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (∑ k, ambientChartEvaluation j (g k) *
      (Pi.single i (show HomogeneousLocalization.Away PS (X j) from x) :
        ι → HomogeneousLocalization.Away PS (X j)) k) =
    ambientChartEvaluation j (g i) * x
  simp [Pi.single_apply, mul_ite]

private theorem actualChartRelation_injection
    {ι κ : Type u} [Fintype ι] [Fintype κ] (j : Fin 4) (r : κ → ι → A) (a : κ) :
    actualFinitePiInjection (HomogeneousLocalization.Away PS (X j)) κ a ≫
      ModuleCat.ofHom (actualDegreeZeroChartRelationMap j r) =
    ∑ i, ModuleCat.ofHom (actualRingMultiplicationMap
      (HomogeneousLocalization.Away PS (X j)) (ambientChartEvaluation j (r a i))) ≫
        actualFinitePiInjection (HomogeneousLocalization.Away PS (X j)) ι i := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext k
  let B := HomogeneousLocalization.Away PS (X j)
  let columns : ι → (ModuleCat.of B B ⟶ ModuleCat.of B (ι → B)) := fun i =>
    ModuleCat.ofHom (actualRingMultiplicationMap B (ambientChartEvaluation j (r a i))) ≫
      actualFinitePiInjection B ι i
  have hleft : (actualFinitePiInjection B κ a ≫
      ModuleCat.ofHom (actualDegreeZeroChartRelationMap j r)).hom x k =
      actualDegreeZeroChartRelationMap j r
        (Pi.single a (show B from x) : κ → B) k :=
    congrArg (fun L : B →ₗ[B] (ι → B) => L (show B from x) k)
      (ModuleCat.hom_comp (actualFinitePiInjection B κ a)
        (ModuleCat.ofHom (actualDegreeZeroChartRelationMap j r)))
  have hright₁ : (∑ i, columns i).hom x k = (∑ i, (columns i).hom) x k :=
    congrArg (fun L : B →ₗ[B] (ι → B) => L (show B from x) k)
      (ModuleCat.hom_sum columns Finset.univ)
  have hright₂ : (∑ i, (columns i).hom) x k = ∑ i, (columns i).hom x k :=
    (congrArg (fun v : ι → B => v k)
      (LinearMap.sum_apply Finset.univ (fun i => (columns i).hom)
        (show B from x))).trans
      (Finset.sum_apply k Finset.univ (fun i => (columns i).hom (show B from x)))
  have hright₃ : (∑ i, (columns i).hom x k) =
      ∑ i, (Pi.single i (ambientChartEvaluation j (r a i) * x) : ι → B) k := rfl
  have hcoordinates : actualDegreeZeroChartRelationMap j r
      (Pi.single a (show B from x) : κ → B) k =
      ∑ i, (Pi.single i (ambientChartEvaluation j (r a i) * x) : ι → B) k := by
    change (∑ b, (Pi.single a (show B from x) : κ → B) b •
      (fun i => ambientChartEvaluation j (r b i))) k = _
    simp [Finset.sum_apply, Pi.single_apply, ite_apply, Pi.smul_apply, smul_eq_mul,
      ite_mul, mul_ite, mul_comm]
  exact hleft.trans (hcoordinates.trans
    (hright₃.symm.trans (hright₂.symm.trans hright₁.symm)))

private lemma mappedFrame_component
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {V W T : C} {M₀ M₁ M₂ : D}
    (a : M₀ ⟶ M₁) (e : M₁ ⟶ F.obj V)
    (t : M₀ ⟶ F.obj W) (v : F.obj T ⟶ M₂)
    (f : W ⟶ V) (g : V ⟶ T) (k : W ⟶ T)
    (hframe : a ≫ e = t ≫ F.map f) (hfg : f ≫ g = k) :
    a ≫ e ≫ F.map g ≫ v = t ≫ F.map k ≫ v := by
  calc
    _ = (a ≫ e) ≫ F.map g ≫ v := (Category.assoc a e (F.map g ≫ v)).symm
    _ = (t ≫ F.map f) ≫ F.map g ≫ v :=
      congrArg (fun z => z ≫ F.map g ≫ v) hframe
    _ = t ≫ F.map (f ≫ g) ≫ v := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := congrArg (fun z => t ≫ F.map z ≫ v) hfg

private lemma frameInjection_inverse
    {C : Type*} [Category C] {O V W U : C}
    (e : V ≅ W) (t : O ≅ U) (a : U ⟶ V) (q : O ⟶ W)
    (h : a ≫ e.hom = t.inv ≫ q) : q ≫ e.inv = t.hom ≫ a := by
  have hh : (t.hom ≫ a) ≫ e.hom = q := by
    rw [Category.assoc, h, ← Category.assoc, t.hom_inv_id, Category.id_comp]
  exact (e.comp_inv_eq).2 hh.symm

private lemma mappedFrame_column
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {ι : Type u} [Fintype ι] (F : C ⥤ D) [F.Additive]
    {W V : C} {U Z : D} (t : F.obj W ≅ U) (v : F.obj V ⟶ Z)
    (a : ι → (W ⟶ W)) (b : ι → (W ⟶ V)) (s : ι → (U ⟶ Z))
    (h : ∀ i, F.map (b i) ≫ v = t.hom ≫ s i) :
    t.inv ≫ F.map (∑ i, a i ≫ b i) ≫ v =
      ∑ i, (t.inv ≫ F.map (a i) ≫ t.hom) ≫ s i := by
  simp only [Functor.map_sum, Functor.map_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i]

/-- Whole generator matrix: canonical tilde of the literal chart matrix,
conjugated by the OWN finite-Pi and tilde-self frames. -/
theorem actualNormalizedSpecUnitGeneratorMatrix_tilde
    {ι : Type u} [Fintype ι] (j : Fin 4) (g : ι → A) :
    (actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) ι).hom ≫
      (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map
        (ModuleCat.ofHom (actualDegreeZeroChartGeneratorMap j g)) ≫
      (tildeSelf (R := CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).hom =
    actualNormalizedSpecUnitGeneratorMatrix j g := by
  classical
  let B := HomogeneousLocalization.Away PS (X j)
  let R := CommRingCat.of B
  let F := tilde.functor R
  let O : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  let family : ι → (Spec R).Modules := fun _ => O
  let e := actualFinitePiTildeUnitIso B ι
  let t := tildeSelf (R := R)
  let c : ι → (O ⟶ O) := fun i => unitEndomorphismOfRegularFunction
    ((Scheme.ΓSpecIso R).inv.hom (ambientChartEvaluation j (g i)))
  apply Sigma.hom_ext
  intro i
  have hcomponent := mappedFrame_component
    (C := ModuleCat B) (D := (Spec R).Modules) F (Sigma.ι family i) e.hom
    t.inv t.hom (actualFinitePiInjection B ι i)
    (ModuleCat.ofHom (actualDegreeZeroChartGeneratorMap j g))
    (ModuleCat.ofHom (actualRingMultiplicationMap B (ambientChartEvaluation j (g i))))
    (actualFinitePiTildeUnitIso_inclusion B ι i) (actualChartGenerator_injection j g i)
  have hcoefficient : t.inv ≫ F.map (ModuleCat.ofHom
      (actualRingMultiplicationMap B (ambientChartEvaluation j (g i)))) ≫ t.hom = c i :=
    actualRingMultiplicationMap_tilde_unitCoefficient B (ambientChartEvaluation j (g i))
  have hdesc : Sigma.ι family i ≫ actualNormalizedSpecUnitGeneratorMatrix j g = c i :=
    Sigma.ι_desc c i
  exact hcomponent.trans (hcoefficient.trans hdesc.symm)

/-- Whole relation matrix: the actual normalized columns, not a replacement
kernel, remain the matrix in the canonical finite-Pi tilde frame. -/
theorem actualNormalizedSpecUnitRelationMatrix_tilde
    {ι κ : Type u} [Fintype ι] [Fintype κ] (j : Fin 4) (r : κ → ι → A) :
    (actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) κ).hom ≫
      (tilde.functor (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).map
        (ModuleCat.ofHom (actualDegreeZeroChartRelationMap j r)) ≫
      (actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) ι).inv =
    actualNormalizedSpecUnitRelationMatrix j r := by
  classical
  let B := HomogeneousLocalization.Away PS (X j)
  let R := CommRingCat.of B
  let F := tilde.functor R
  letI : Preadditive (Spec R).Modules :=
    inferInstanceAs (Preadditive (SheafOfModules.{u} (Spec R).ringCatSheaf))
  letI : F.IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
  letI : PreservesBinaryBiproducts F :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  letI : F.Additive := CategoryTheory.Functor.additive_of_preservesBinaryBiproducts F
  let O : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  let family : ι → (Spec R).Modules := fun _ => O
  let sourceFamily : κ → (Spec R).Modules := fun _ => O
  let e := actualFinitePiTildeUnitIso B ι
  let eκ := actualFinitePiTildeUnitIso B κ
  let t := tildeSelf (R := R)
  let c : κ → ι → (O ⟶ O) := fun a i => unitEndomorphismOfRegularFunction
    ((Scheme.ΓSpecIso R).inv.hom (ambientChartEvaluation j (r a i)))
  let column : κ → (O ⟶ ∐ family) := fun a => ∑ i, c a i ≫ Sigma.ι family i
  have hinj (i : ι) : F.map (actualFinitePiInjection B ι i) ≫ e.inv =
      t.hom ≫ Sigma.ι family i :=
    frameInjection_inverse (C := (Spec R).Modules) e t (Sigma.ι family i)
      (F.map (actualFinitePiInjection B ι i))
      (actualFinitePiTildeUnitIso_inclusion B ι i)
  apply Sigma.hom_ext
  intro a
  let mult : ι → (ModuleCat.of B B ⟶ ModuleCat.of B B) := fun i =>
    ModuleCat.ofHom (actualRingMultiplicationMap B (ambientChartEvaluation j (r a i)))
  have hcomponent := mappedFrame_component
    (C := ModuleCat B) (D := (Spec R).Modules) F (Sigma.ι sourceFamily a) eκ.hom
    t.inv e.inv (actualFinitePiInjection B κ a)
    (ModuleCat.ofHom (actualDegreeZeroChartRelationMap j r))
    (∑ i, mult i ≫ actualFinitePiInjection B ι i)
    (actualFinitePiTildeUnitIso_inclusion B κ a) (actualChartRelation_injection j r a)
  have hcolumn := mappedFrame_column (C := ModuleCat B) (D := (Spec R).Modules)
    F t e.inv mult (actualFinitePiInjection B ι) (fun i => Sigma.ι family i) hinj
  letI : AddCommGroup (O ⟶ ∐ family) :=
    @Preadditive.homGroup (Spec R).Modules
      (inferInstance : Category (Spec R).Modules)
      (inferInstance : Preadditive (Spec R).Modules) O (∐ family)
  have hsum : (∑ i, (show O ⟶ ∐ family from
      (t.inv ≫ F.map (mult i) ≫ t.hom) ≫ Sigma.ι family i)) = column a := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z : O ⟶ O => z ≫ Sigma.ι family i)
      (actualRingMultiplicationMap_tilde_unitCoefficient B (ambientChartEvaluation j (r a i)))
  have hdesc : Sigma.ι sourceFamily a ≫ actualNormalizedSpecUnitRelationMatrix j r = column a :=
    Sigma.ι_desc column a
  exact hcomponent.trans (hcolumn.trans (hsum.trans hdesc.symm))

private theorem framedMatrices_zero
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (S : ShortComplex C) {M₁ M₂ M₃ : C}
    (e₁ : M₁ ≅ S.X₁) (e₂ : M₂ ≅ S.X₂) (e₃ : S.X₃ ≅ M₃)
    (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
    (hf : e₁.hom ≫ S.f ≫ e₂.inv = f)
    (hg : e₂.hom ≫ S.g ≫ e₃.hom = g) : f ≫ g = 0 := by
  rw [← hf, ← hg]
  simp only [Category.assoc, e₂.inv_hom_id_assoc, S.zero_assoc, comp_zero, zero_comp]

/-- The literal Spec-unit matrices form an actual short complex, using only
exactly the original homogeneous generator/kernel-relation data. -/
def actualNormalizedSpecUnitPresentationComplex
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) :
    ShortComplex (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules :=
  ShortComplex.mk (actualNormalizedSpecUnitRelationMatrix j r)
    (actualNormalizedSpecUnitGeneratorMatrix j g)
    (framedMatrices_zero (actualDegreeZeroChartPresentation_tildeComplex I g r hg hr j)
      (actualFinitePiTildeUnitIso _ κ) (actualFinitePiTildeUnitIso _ ι) tildeSelf
      _ _ (actualNormalizedSpecUnitRelationMatrix_tilde j r)
      (actualNormalizedSpecUnitGeneratorMatrix_tilde j g))

/-- Exactness of the actual normalized unit matrices is DERIVED from tilde
of the OWN homogeneous presentation on this native chart. -/
theorem actualNormalizedSpecUnitPresentationComplex_exact
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) : (actualNormalizedSpecUnitPresentationComplex I g r hg hr j).Exact := by
  let S := actualDegreeZeroChartPresentation_tildeComplex I g r hg hr j
  let T := actualNormalizedSpecUnitPresentationComplex I g r hg hr j
  let e₁ := actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) κ
  let e₂ := actualFinitePiTildeUnitIso (HomogeneousLocalization.Away PS (X j)) ι
  let e₃ := tildeSelf (R := CommRingCat.of (HomogeneousLocalization.Away PS (X j)))
  have hf : e₁.hom ≫ S.f ≫ e₂.inv = T.f := actualNormalizedSpecUnitRelationMatrix_tilde j r
  have hg' : e₂.hom ≫ S.g ≫ e₃.hom = T.g := actualNormalizedSpecUnitGeneratorMatrix_tilde j g
  let E : T ≅ S := ShortComplex.isoMk e₁ e₂ e₃.symm
    ((e₂.comp_inv_eq).mp hf)
    ((e₃.eq_comp_inv).mpr hg')
  exact ShortComplex.exact_of_iso E.symm
    (actualDegreeZeroChartPresentation_tildeComplex_exact I g r hg hr j)

end PfaffianDescent.Coray
