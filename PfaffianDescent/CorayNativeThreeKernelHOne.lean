import PfaffianDescent.SheafModuleOverExtComparison
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! Natural native categorical adapters for a third actual syzygy map.
Source only, UNVERIFIED. These are NOT whole-ideal vanishing producers.
The actual caller must internally construct its three exact sequences. -/
noncomputable section
namespace PfaffianDescent.Coray
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u

/-- An exact literal third relation matrix induces an epimorphism to the
SAME second native kernel. The equality to the original matrix is retained. -/
theorem nativeThirdKernelSequence_of_exactRelationPair
    {C : Type*} [Category C] [Abelian C]
    {F₀ F₁ F₂ J : C} (a : F₀ ⟶ J) (r : F₁ ⟶ F₀) (hz : r ≫ a = 0)
    (s : F₂ ⟶ F₁) (hs : s ≫ r = 0)
    (hex : (ShortComplex.mk s r hs).Exact) :
    let b := kernel.lift a r hz
    ∃ hsb : s ≫ b = 0,
      let c := kernel.lift b s hsb
      Epi c ∧ c ≫ kernel.ι b = s ∧
        (ShortComplex.mk (kernel.ι c) c (kernel.condition c)).ShortExact := by
  dsimp only
  let b := kernel.lift a r hz
  have hb : b ≫ kernel.ι a = r := kernel.lift_ι a r hz
  have hsb : s ≫ b = 0 := by
    apply (cancel_mono (kernel.ι a)).mp
    exact (Category.assoc s b (kernel.ι a)).trans
      ((congrArg (fun q => s ≫ q) hb).trans (hs.trans zero_comp.symm))
  let S : ShortComplex C := ShortComplex.mk s b hsb
  let T : ShortComplex C := ShortComplex.mk s r hs
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 F₂
      τ₂ := 𝟙 F₁
      τ₃ := kernel.ι a
      comm₁₂ := by
        change (𝟙 F₂) ≫ s = s ≫ (𝟙 F₁)
        simp only [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        change (𝟙 F₁) ≫ r = b ≫ kernel.ι a
        simpa only [Category.id_comp] using hb.symm }
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hex
  let c := kernel.lift b s hsb
  letI : Epi c := hS.epi_kernelLift
  exact ⟨hsb, inferInstance, kernel.lift_ι b s hsb,
    { exact := ShortComplex.exact_kernel c }⟩

/-- Native three-sequence consequence in degree ONE. All Ext objects and
literal kernel lifts use the original category dictionaries. No degree2
vanishing result is relabelled as degree1. -/
theorem nativeExt_threeKernelSequences_subsingleton
    {C : Type*} [Category C] [Abelian C] [HasExt.{u} C]
    (P : C) {F₀ F₁ F₂ J : C} (a : F₀ ⟶ J) (r : F₁ ⟶ F₀)
    (hz : r ≫ a = 0) (s : F₂ ⟶ F₁)
    (hs : s ≫ kernel.lift a r hz = 0)
    (h₀ : (ShortComplex.mk (kernel.ι a) a (kernel.condition a)).ShortExact)
    (h₁ : (ShortComplex.mk (kernel.ι (kernel.lift a r hz))
      (kernel.lift a r hz) (kernel.condition (kernel.lift a r hz))).ShortExact)
    (h₂ : (ShortComplex.mk (kernel.ι (kernel.lift (kernel.lift a r hz) s hs))
      (kernel.lift (kernel.lift a r hz) s hs)
      (kernel.condition (kernel.lift (kernel.lift a r hz) s hs))).ShortExact)
    [Subsingleton (Ext.{u} P F₀ 1)] [Subsingleton (Ext.{u} P F₁ 2)]
    [Subsingleton (Ext.{u} P F₂ 3)]
    [Subsingleton (Ext.{u} P (kernel (kernel.lift (kernel.lift a r hz) s hs)) 4)] :
    Subsingleton (Ext.{u} P J 1) := by
  let b := kernel.lift a r hz
  let c := kernel.lift b s hs
  let S₂ : ShortComplex C := ShortComplex.mk (kernel.ι c) c (kernel.condition c)
  let S₁ : ShortComplex C := ShortComplex.mk (kernel.ι b) b (kernel.condition b)
  let S₀ : ShortComplex C := ShortComplex.mk (kernel.ι a) a (kernel.condition a)
  letI : Subsingleton (Ext.{u} P (kernel b) 3) :=
    ext_subsingleton_of_middle_and_next_left P S₂ h₂ 3
  letI : Subsingleton (Ext.{u} P (kernel a) 2) :=
    ext_subsingleton_of_middle_and_next_left P S₁ h₁ 2
  exact ext_subsingleton_of_middle_and_next_left P S₀ h₀ 1

end PfaffianDescent.Coray
