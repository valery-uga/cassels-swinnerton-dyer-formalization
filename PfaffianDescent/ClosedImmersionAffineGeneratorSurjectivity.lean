import PfaffianDescent.ClosedImmersionIdealModuleAffineFree
import Mathlib.RingTheory.Ideal.Operations

/-! SOURCE ONLY / UNVERIFIED. Generic finite-generator lifting into the
actual closed-immersion ideal module. This is an intermediate affine algebra
lemma; the geometric caller must derive its generator identities internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u v

/-- The linear-combination computation is proved before actual scheme
section and scalar dictionaries are substituted. -/
private theorem affineGenerator_linearCombination_image
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] (q : M →ₗ[R] R)
    (a : ι → M) (c : ι → R) (hq : ∀ r, q (a r) = c r) (b : ι → R) :
    q (∑ r, b r • a r) = ∑ r, b r * c r := by
  simp only [map_sum, map_smul, hq, smul_eq_mul]

/-- A finite collection of actual source sections whose images generate the
actual affine immersion ideal makes the component map surjective. No
regularity, reducedness or etaleness is involved. -/
theorem closedImmersionModule_affineGeneratorMap_surjective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : X.Modules) (φ : M ⟶ IdealSheafDataModule.closedImmersionModule i)
    (V : X.affineOpens) {ι : Type v} [Fintype ι]
    (a : ι → Γ(M, V.1)) (c : ι → Γ(X, V.1))
    (hgen : i.ker.ideal V = Ideal.span (Set.range c))
    (himage : ∀ r, ((φ ≫ IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
      (op V.1)) (a r) = c r) :
    Function.Surjective (φ.val.app (op V.1)) := by
  let I := IdealSheafDataModule.closedImmersionModule i
  let ψ := IdealSheafDataModule.closedImmersionModuleToUnit i
  letI : Module (X.presheaf.obj (op V.1))
      ((M.val.obj (op V.1) : ModuleCat _)) :=
    (M.val.obj (op V.1)).isModule
  letI : Module (X.presheaf.obj (op V.1))
      ((I.val.obj (op V.1) : ModuleCat _)) :=
    (I.val.obj (op V.1)).isModule
  let q : ((M.val.obj (op V.1) : ModuleCat _)) →ₗ[X.presheaf.obj (op V.1)]
      (X.presheaf.obj (op V.1)) := ((φ ≫ ψ).val.app (op V.1)).hom
  have hq (r : ι) : q (a r) = c r := himage r
  let e := IdealSheafDataModule.closedImmersionModule_affineSectionsLinearEquivIdeal i V
  intro m
  have hm : (show X.presheaf.obj (op V.1) from ψ.val.app (op V.1) m) ∈
      Ideal.span (Set.range c) := by
    rw [← hgen]
    exact IdealSheafDataModule.closedImmersionModule_section_mem_ker_ideal i V m
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hm
  refine ⟨∑ r, b r • a r, ?_⟩
  apply e.injective
  apply Subtype.ext
  change q (∑ r, b r • a r) =
    (show X.presheaf.obj (op V.1) from ψ.val.app (op V.1) m)
  exact (affineGenerator_linearCombination_image q a c hq b).trans hb

/-- Surjectivity on affine subopens of a genuine covering implies Epi for
an actual module-sheaf morphism. This supplies the sheaf-local final step
without assuming quasi-coherent-section exactness globally. -/
theorem schemeModule_epi_of_affineSubopens_cover_surjective
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type v} (U : ι → X.Opens)
    (hU : ⨆ r, U r = ⊤)
    (hφ : ∀ r (V : X.affineOpens), V.1 ≤ U r →
      Function.Surjective (φ.val.app (op V.1))) : Epi φ := by
  constructor
  intro W g h H
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  ext V s
  apply TopCat.Presheaf.IsSheaf.section_ext W.isSheaf
  intro x hx
  have hxU : x ∈ ⨆ r, U r := by rw [hU]; trivial
  obtain ⟨r, hr⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V.unop ⊓ U r from ⟨hx, hr⟩) (V.unop ⊓ U r).2
  let A' : X.affineOpens := ⟨A, hA⟩
  let hAV' : A ≤ V.unop := hAV.trans inf_le_left
  let sA := N.presheaf.map (homOfLE hAV').op s
  obtain ⟨t, ht⟩ := hφ r A' (hAV.trans inf_le_right) sA
  refine ⟨A, hAV', hxA, ?_⟩
  have hg := ConcreteCategory.congr_hom (g.val.naturality (homOfLE hAV').op) s
  have hh := ConcreteCategory.congr_hom (h.val.naturality (homOfLE hAV').op) s
  have he := ConcreteCategory.congr_hom
    (congrArg (fun k => k.val.app (op A)) H) t
  have he' : g.val.app (op A) sA = h.val.app (op A) sA := by
    rw [← ht]
    exact he
  change W.presheaf.map (homOfLE hAV').op (g.val.app V s) =
    W.presheaf.map (homOfLE hAV').op (h.val.app V s)
  exact hg.symm.trans (he'.trans hh)

end PfaffianDescent
