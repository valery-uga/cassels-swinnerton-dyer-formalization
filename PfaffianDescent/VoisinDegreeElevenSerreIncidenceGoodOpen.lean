import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGenericFibre

/-! # Finite zero together with an actual additional incidence open

For residual degree eight, the additional open will express simplicity of
the three marked zeros.  Its construction is separate; these lemmas preserve
it during dominance and ground-field rational parameter selection.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The finite-zero open intersected with an actual additional open. -/
def serreIncidenceGoodOpen {Z I : Scheme.{u}}
    (zero : Z ⟶ I) [IsProper zero] (W : I.Opens) : I.Opens :=
  cubicClosedPointSerreFiniteZeroResidual_goodOpen zero ⊓ W

/-- A canonical parameter with finite zero and lying in the additional open
puts the generic configuration in the image of both conditions together. -/
theorem serreIncidenceGoodOpen_genericPoint
    {Z I B : Scheme.{u}} (zero : Z ⟶ I) [IsProper zero]
    (W : I.Opens) (π : I ⟶ B) [IsIntegral B] (hπ : IsOpenMap π)
    (i : I) (hi : (zero ⁻¹' {i}).Finite) (hiW : i ∈ W) :
    ∃ j : I, π j = genericPoint B ∧ j ∈ serreIncidenceGoodOpen zero W := by
  have hiV : i ∈ serreIncidenceGoodOpen zero W :=
    ⟨cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre zero i hi, hiW⟩
  have hopen : IsOpen (π '' (serreIncidenceGoodOpen zero W : Set I)) :=
    hπ _ (serreIncidenceGoodOpen zero W).isOpen
  have hη : genericPoint B ∈ π '' (serreIncidenceGoodOpen zero W : Set I) :=
    (genericPoint_specializes (π i)).mem_open hopen ⟨i, hiV, rfl⟩
  obtain ⟨j, hjV, hj⟩ := hη
  exact ⟨j, hj, hjV⟩

theorem serreIncidenceGoodOpen_genericFibre_nonempty
    {Z I B : Scheme.{u}} (zero : Z ⟶ I) [IsProper zero]
    (W : I.Opens) (π : I ⟶ B) [IsIntegral B] (hπ : IsOpenMap π)
    (i : I) (hi : (zero ⁻¹' {i}).Finite) (hiW : i ∈ W) :
    (((π.fiberι (genericPoint B)) ⁻¹ᵁ serreIncidenceGoodOpen zero W) :
      Set (π.fiber (genericPoint B))).Nonempty := by
  obtain ⟨j, hj, hjV⟩ := serreIncidenceGoodOpen_genericPoint zero W π hπ i hi hiW
  refine ⟨(π.fiberHomeo (genericPoint B)).symm ⟨j, hj⟩, ?_⟩
  change π.fiberι (genericPoint B) _ ∈ serreIncidenceGoodOpen zero W
  simpa only [Scheme.Hom.fiberι_fiberHomeo_symm] using hjV

/-- Rational selection on the actual projective kernel retains the marked
simple-zero open and the exact configuration morphism, while making its zero
scheme finite over the same ground field. -/
theorem serreIncidenceProjectivePlane_exists_good_parameter_over
    {F : Type u} [Field F] [Infinite F] {Z I B : Scheme.{u}}
    (zero : Z ⟶ I) [IsProper zero] (W : I.Opens) (π : I ⟶ B)
    (b : Spec (.of F) ⟶ B) (frame : serreKernelProjectivePlane F ⟶ I)
    (hframe : frame ≫ π = serreKernelProjectivePlaneToBase F ≫ b)
    (hne : ((frame ⁻¹ᵁ serreIncidenceGoodOpen zero W) :
      Set (serreKernelProjectivePlane F)).Nonempty) :
    ∃ s : Spec (.of F) ⟶ I, s ≫ π = b ∧
      s (IsLocalRing.closedPoint F) ∈ W ∧ IsFinite (pullback.snd zero s) := by
  let U := frame ⁻¹ᵁ serreIncidenceGoodOpen zero W
  obtain ⟨q, hq⟩ := nonempty_open_projectiveSpace_has_rational_section U hne
  refine ⟨q ≫ U.ι ≫ frame, ?_, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hframe]
    have hq' : q ≫ U.ι ≫ serreKernelProjectivePlaneToBase F = 𝟙 _ := hq
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun f => f ≫ b) hq'
  · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (q (IsLocalRing.closedPoint F)).2.2
  · apply serreIncidenceFiniteZero_fieldPoint
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (q (IsLocalRing.closedPoint F)).2.1

end PfaffianDescent
