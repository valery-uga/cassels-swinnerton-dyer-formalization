import PfaffianDescent.CorayPositiveFiniteCoproductCohomology
import PfaffianDescent.CorayHypersurfaceTwistAmbientFiniteCohomology
import PfaffianDescent.ExtMapFixedSource

/-! SOURCE ONLY / UNVERIFIED. Native scalar-preserving finite coproduct Ext
and finite right cohomology from an actual short exact sequence. No RR,
duality, numerical bound, or eventual vanishing is supplied or claimed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
variable {K : Type u} [Field K]

/-- The canonical second-variable Ext biproduct decomposition is linear
for the category's already installed scalar action. -/
def nativeExtBiproductLinearEquiv
    {D : Type*} [Category D] [Abelian D] [HasExt.{u} D] [Linear K D]
    [HasFiniteBiproducts D]
    {ι : Type*} [Fintype ι] (P : D) (M : ι → D) (n : ℕ) :
    Ext.{u} P (⨁ M) n ≃ₗ[K] (∀ i, Ext.{u} P (M i) n) := by
  refine
    { toAddEquiv := Ext.addEquivBiproduct P (biproduct.isBilimit M) n
      map_smul' := ?_ }
  intro c z
  ext i
  change (c • z).comp (Ext.mk₀ (biproduct.π M i)) (add_zero n) =
    c • z.comp (Ext.mk₀ (biproduct.π M i)) (add_zero n)
  exact Ext.smul_comp z (Ext.mk₀ (biproduct.π M i)) (add_zero n) c

/-- Canonical coefficient postcomposition retains the installed scalar
structure; the additive equivalence is not silently used as a linear one. -/
def nativeExtRightIsoLinearEquiv
    {D : Type*} [Category D] [Abelian D] [HasExt.{u} D] [Linear K D]
    (P : D) {M N : D} (e : M ≅ N) (n : ℕ) :
    Ext.{u} P M n ≃ₗ[K] Ext.{u} P N n := by
  refine { toAddEquiv := extPostcompIsoOfIso e, map_smul' := ?_ }
  intro c z
  change (c • z).comp (Ext.mk₀ e.hom) (add_zero n) =
    c • z.comp (Ext.mk₀ e.hom) (add_zero n)
  exact Ext.smul_comp z (Ext.mk₀ e.hom) (add_zero n) c

/-- Finite original-scalar Ext of each finite summand makes Ext of the
actual native coproduct finite. -/
theorem nativeExt_finiteCoproduct_target_finite
    {D : Type*} [Category D] [Abelian D] [HasExt.{u} D] [Linear K D]
    {ι : Type*} [Fintype ι] (P : D) (M : ι → D) (n : ℕ)
    [∀ i, Module.Finite K (Ext.{u} P (M i) n)] :
    Module.Finite K (Ext.{u} P (∐ M) n) := by
  letI : HasFiniteBiproducts D := CategoryTheory.Abelian.hasFiniteBiproducts
  letI : Module.Finite K (Ext.{u} P (⨁ M) n) :=
    Module.Finite.equiv (nativeExtBiproductLinearEquiv P M n).symm
  exact Module.Finite.equiv
    (nativeExtRightIsoLinearEquiv P (biproduct.isoCoproduct M) n)

/-- Actual short exactness and zero next-left Ext give actual surjectivity
of the middle-to-right coefficient map. No comparison map is a premise. -/
theorem schemeModuleRestriction_rightCohomology_finite_of_middle_finite_and_next_left_zero
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (schemeModuleCohomology X S.X₁ (n + 1))] :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (schemeModuleCohomology X S.X₂ n) →
      Module.Finite K (schemeModuleCohomology X S.X₃ n) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hfinite
  letI : Module.Finite K (schemeModuleCohomology X S.X₂ n) := hfinite
  let g : schemeModuleCohomology X S.X₂ n →ₗ[K]
      schemeModuleCohomology X S.X₃ n :=
    Ext.postcompOfLinear (Ext.mk₀ S.g) K
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) (add_zero n)
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) hS z rfl
      (show z.comp hS.extClass (show n + 1 = n + 1 from rfl) = 0 from
        Subsingleton.elim _ _)
    exact ⟨a, ha⟩
  exact Module.Finite.of_surjective g hg

end PfaffianDescent.Coray
