import PfaffianDescent.SchemeModuleSignedPointTensorStalkRangeStep
import PfaffianDescent.ScaledRingRangeProduct
import PfaffianDescent.SchemeModuleFixedFrameUnitStalkFunctionField

/-! Full local image of the SAME actual finite signed tensor word.
One complement, its canonical recursive chart and one actual generator
at the fixed test point are retained at every literal fold step.
No final image, valuation, tensor-comparison or injection certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Only an abbreviation for the original map's underlying function;
it exposes the native module once, without constructing any new map. -/
private abbrev fixedFrameStalkFunction
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (C : X.Opens) [Nonempty C]
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (x : X) :
    M.presheaf.stalk x → X.functionField := by
  letI := schemeModuleStalkModule M x
  exact fun a => schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x a

private theorem range_product_scaled_zpow
    {R F A B : Type*} [CommRing R] [Field F]
    (κ : R →+* F) (z : F) (hz : z ≠ 0) (a b : ℤ)
    (f : A → F) (g : B → F)
    (hf : Set.range f = Set.range (fun r : R => κ r * z ^ a))
    (hg : Set.range g = Set.range (fun r : R => κ r * z ^ b)) :
    Set.range (fun p : A × B => f p.1 * g p.2) =
      Set.range (fun r : R => κ r * z ^ (a + b)) := by
  have hprod : Set.range (fun p : A × B => f p.1 * g p.2) =
      Set.range (fun p : R × R => (κ p.1 * z ^ a) * (κ p.2 * z ^ b)) := by
    apply Set.Subset.antisymm
    · rintro v ⟨p, hp⟩
      have hrange : f p.1 ∈ Set.range (fun r : R => κ r * z ^ a) := hf ▸ ⟨p.1, rfl⟩
      have srange : g p.2 ∈ Set.range (fun r : R => κ r * z ^ b) := hg ▸ ⟨p.2, rfl⟩
      obtain ⟨r, hr⟩ := hrange
      obtain ⟨s, hs⟩ := srange
      exact ⟨⟨r, s⟩, (congrArg₂ (fun u v : F => u * v) hr hs).trans hp⟩
    · rintro v ⟨p, hp⟩
      have frange : κ p.1 * z ^ a ∈ Set.range f := hf.symm ▸ ⟨p.1, rfl⟩
      have grange : κ p.2 * z ^ b ∈ Set.range g := hg.symm ▸ ⟨p.2, rfl⟩
      obtain ⟨r, hr⟩ := frange
      obtain ⟨s, hs⟩ := grange
      exact ⟨⟨r, s⟩, (congrArg₂ (fun u v : F => u * v) hr hs).trans hp⟩
  exact hprod.trans (ringHom_scaledRangeProduct_zpow κ z hz a b)

/-- FULL actual word-stalk image is the original local-ring image scaled
by the SAME actual generator germ to negative-count minus positive-count
at P. The genuine word frame/common complement are constructed internally.
The only generic geometric inputs are nongeneric selected points, actual
ideal rank-one geometry, and an actual regular-principal chart at P. -/
theorem schemeModuleSignedPointTensorWord_stalkRange_zpow
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (V : X.affineOpens) (hPV : P.1 ∈ V.1)
    (ops : List (closedPoints X × Bool))
    (hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint X)
    (hM : ∀ Q : closedPoints X,
      let i := X.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
      schemeModuleLocallyRankOne (closedImmersionModule i)) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∀ (m : M.val.obj (op V.1)),
      @IsRegular (Γ(X, V.1)) inferInstance
        ((closedImmersionModuleToUnit i).val.app (op V.1) m) →
      i.ker.ideal V = Ideal.span
        ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1)) →
      let zP := X.presheaf.germ V.1 P.1 hPV
        ((closedImmersionModuleToUnit i).val.app (op V.1) m)
      let C := schemeSignedPointTensorWordComplementOpen ops
      letI : Nonempty C := ⟨⟨genericPoint X, schemeSignedPointTensorWordComplementOpen_generic_mem ops hP⟩⟩
      let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      let W := schemeModuleIteratedSignedClosedPointTensor O ops
      letI := schemeModuleStalkModule W P.1
      Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi W C
        (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
          (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)) P.1) =
        Set.range (fun r : X.presheaf.stalk P.1 =>
          @HMul.hMul X.functionField X.functionField X.functionField inferInstance
            (algebraMap (X.presheaf.stalk P.1) X.functionField r)
            ((algebraMap (X.presheaf.stalk P.1) X.functionField zP) ^
              schemeSignedPointTensorWordLocalOrder P ops)) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro m hreg hprincipal
  let κ := algebraMap (X.presheaf.stalk P.1) X.functionField
  let zP : X.presheaf.stalk P.1 := X.presheaf.germ V.1 P.1 hPV
    ((closedImmersionModuleToUnit i).val.app (op V.1) m)
  let z : X.functionField := κ zP
  have hzP : zP ≠ 0 :=
    (closedPointIdeal_affineRegularGenerator_germ_irreducible X P V hPV m hreg hprincipal).ne_zero
  have hz : z ≠ 0 := by
    intro he
    apply hzP
    apply IsFractionRing.injective (X.presheaf.stalk P.1) X.functionField
    exact he.trans κ.map_zero.symm
  let C := schemeSignedPointTensorWordComplementOpen ops
  letI : Nonempty C := ⟨⟨genericPoint X, schemeSignedPointTensorWordComplementOpen_generic_mem ops hP⟩⟩
  have hiter : ∀ (word : List (closedPoints X × Bool))
      (hexcludes : ∀ operation ∈ word, operation.1.1 ∉ C)
      (L : X.Modules) (hL : schemeModuleLocallyRankOne L)
      (eL : L.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C) (a : ℤ),
      Set.range (fixedFrameStalkFunction pi L C eL P.1) =
          Set.range (fun r : X.presheaf.stalk P.1 => κ r * z ^ a) →
      Set.range (fixedFrameStalkFunction pi (schemeModuleIteratedSignedClosedPointTensor L word) C
        (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C word hexcludes L eL) P.1) =
          Set.range (fun r : X.presheaf.stalk P.1 =>
            κ r * z ^ (a + schemeSignedPointTensorWordLocalOrder P word)) := by
    intro word
    induction word with
    | nil =>
      intro hexcludes L hL eL a hstart
      simpa only [schemeModuleIteratedSignedClosedPointTensor, List.foldl_nil,
        schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso,
        schemeSignedPointTensorWordLocalOrder, List.map_nil, List.sum_nil, add_zero] using hstart
    | cons operation word ih =>
      intro hexcludes L hL eL a hstart
      let hop := hexcludes operation (List.mem_cons_self ..)
      let T := schemeModuleSignedClosedPointTensor operation L
      let eT := schemeModuleSignedClosedPointTensorOverCanonicalIso operation C hop L eL
      have hT : schemeModuleLocallyRankOne T :=
        schemeModuleSignedClosedPointTensor_locallyRankOne operation L hM hL
      have hfactor := schemeModuleSignedClosedPointFactor_stalkRange_localOrder
        pi P V hPV C operation hop m hreg hprincipal
      have hstep : Set.range (fixedFrameStalkFunction pi T C eT P.1) =
          Set.range (fun r : X.presheaf.stalk P.1 =>
            κ r * z ^ (a + schemeSignedClosedPointTensorLocalOrder P operation)) :=
        (schemeModuleSignedClosedPointTensor_stalkRange_product pi operation C hop L hL eL hM P.1).trans
          (range_product_scaled_zpow κ z hz a (schemeSignedClosedPointTensorLocalOrder P operation)
            (fixedFrameStalkFunction pi L C eL P.1)
            (fixedFrameStalkFunction pi (schemeModuleSignedClosedPointFactor operation) C
              (schemeModuleSignedClosedPointFactorOverCanonicalIso operation C hop) P.1)
            hstart hfactor)
      let htail : ∀ op ∈ word, op.1.1 ∉ C := fun op hmem => hexcludes op (List.mem_cons_of_mem _ hmem)
      have h := ih htail T hT eT (a + schemeSignedClosedPointTensorLocalOrder P operation) hstep
      change Set.range (fixedFrameStalkFunction pi (schemeModuleIteratedSignedClosedPointTensor T word) C
        (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C word htail T eT) P.1) = _
      exact h.trans (congrArg (fun b : ℤ => Set.range (fun r : X.presheaf.stalk P.1 => κ r * z ^ b))
        (show (a + schemeSignedClosedPointTensorLocalOrder P operation) +
            schemeSignedPointTensorWordLocalOrder P word =
          a + schemeSignedPointTensorWordLocalOrder P (operation :: word) from by
            simp only [schemeSignedPointTensorWordLocalOrder, List.map_cons, List.sum_cons, add_assoc]))
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  have hbase : Set.range (fixedFrameStalkFunction pi O C (Iso.refl _) P.1) =
      Set.range (fun r : X.presheaf.stalk P.1 => κ r * z ^ (0 : ℤ)) := by
    simpa only [zpow_zero, mul_one] using
      (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_unit_injective_and_range pi C P.1).2
  have h := hiter ops (schemeSignedPointTensorWordComplementOpen_excludes ops) O hO (Iso.refl _) 0 hbase
  simpa only [zero_add] using h

end PfaffianDescent.Coray
