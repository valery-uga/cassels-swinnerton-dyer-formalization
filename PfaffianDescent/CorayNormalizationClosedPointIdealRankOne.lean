import PfaffianDescent.CorayNormalizationClosedPointIdealNeighborhood
import PfaffianDescent.ClosedImmersionIdealModuleCartierChart
import PfaffianDescent.SheafFreeCover
import PfaffianDescent.VoisinPositiveTwistTriviality
import Mathlib.Algebra.Category.Ring.Constructions

/-! Actual rank-one charts of the SAME closed-point ideal on ALL of the
original normalization. The chart map is induced by an ACTUAL ideal-module
section and its original inclusion. No local-free/chart certificate occurs
in the primitive p/q endpoint. Positive inverse pole module is a later stage.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME actual point kernel ideal is the unit ideal on an affine open
which excludes the actual point. This includes empty affine opens. -/
theorem closedPointIdeal_affine_eq_top_away
    (X : Scheme.{u}) (P : closedPoints X) (U : X.affineOpens)
    (hPU : P.1 ∉ U.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    i.ker.ideal U = ⊤ := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  have hpre : i ⁻¹ᵁ U.1 = ⊥ := by
    ext z
    change i z ∈ U.1 ↔ False
    refine ⟨fun hz => hPU ?_, False.elim⟩
    simpa only [i, Scheme.fromSpecResidueField_apply] using hz
  letI : Subsingleton Γ(Spec (X.residueField P.1), i ⁻¹ᵁ U.1) :=
    CommRingCat.subsingleton_of_isTerminal
      ((Spec (X.residueField P.1)).sheaf.isTerminalOfEqEmpty hpre)
  rw [Scheme.Hom.ker_apply]
  apply top_unique
  intro a _
  change (i.app U.1).hom a = 0
  exact Subsingleton.elim _ _

/-- Upgrade a genuine actual regular affine generator to the actual
section-induced unit-to-ideal SHEAF isomorphism. Principality on every
smaller affine open is derived from the original ideal restriction law. -/
theorem closedImmersionModule_affineSection_isIso_of_regularPrincipal
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens)
    (m : (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj (op U.1))
    (hreg : @IsRegular (Γ(X, U.1)) inferInstance
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m))
    (hprincipal : i.ker.ideal U = Ideal.span
      ({(IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m} :
        Set Γ(X, U.1))) :
    IsIso (schemeModuleSectionOnOpenHom
      (IdealSheafDataModule.closedImmersionModule i) U.1 m) := by
  let z : Γ(X, U.1) :=
    (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m
  apply closedImmersionModule_sectionOnAffineOpen_isIso i U z hreg ?_ m rfl
  intro W hWU
  calc
    i.ker.ideal W = (i.ker.ideal U).map
        (X.presheaf.map (homOfLE hWU).op).hom := (i.ker.map_ideal (U := W) (V := U) hWU).symm
    _ = Ideal.span ({X.presheaf.map (homOfLE hWU).op z} : Set Γ(X, W.1)) := by
      rw [hprincipal, Ideal.map_span, Set.image_singleton]

/-- Away from P the actual ideal has a section mapping to 1, whose actual
section-induced chart hom is an isomorphism. Its original inclusion is
retained, rather than replacing the ideal module by an abstract unit. -/
theorem closedPointIdeal_affine_unitGenerator_away
    (X : Scheme.{u}) (P : closedPoints X) (U : X.affineOpens)
    (hPU : P.1 ∉ U.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
    ∃ m : M.val.presheaf.obj (op U.1),
      (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m =
        (1 : Γ(X, U.1)) ∧
      IsIso (schemeModuleSectionOnOpenHom M U.1 m) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  have htop : i.ker.ideal U = ⊤ := closedPointIdeal_affine_eq_top_away X P U hPU
  have hmem : (1 : Γ(X, U.1)) ∈ i.ker.ideal U := by rw [htop]; trivial
  obtain ⟨m, hm⟩ :=
    IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem i U 1 hmem
  refine ⟨m, hm, ?_⟩
  apply closedImmersionModule_affineSection_isIso_of_regularPrincipal i U m
  · rw [hm]
    exact isRegular_one
  · rw [hm, htop, Ideal.span_singleton_one]

/-- The actual affine generator at the point and the actual unit generator
on its complement give charts everywhere, before any normalization is inserted. -/
private theorem closedPointIdeal_rankOne_chart_of_regularGenerator
    (N : Scheme.{u}) (P : closedPoints N)
    (hgen :
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
      ∃ U : N.affineOpens, P.1 ∈ U.1 ∧ ∃ m : M.val.presheaf.obj (op U.1),
        let z : Γ(N, U.1) :=
          (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m
        IsRegular z ∧ i.ker.ideal U = Ideal.span ({z} : Set Γ(N, U.1)))
    (x : N) :
    let i := N.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
    ∃ U : N.affineOpens, x ∈ U.1 ∧ ∃ m : M.val.presheaf.obj (op U.1),
      IsIso (schemeModuleSectionOnOpenHom M U.1 m) ∧
      let z : Γ(N, U.1) :=
        (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m
      IsRegular z ∧ i.ker.ideal U = Ideal.span ({z} : Set Γ(N, U.1)) := by
  classical
  dsimp only at hgen ⊢
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  by_cases hx : x = P.1
  · subst x
    obtain ⟨U, hPU, m, hmreg, hmprincipal⟩ := hgen
    exact ⟨U, hPU, m,
      closedImmersionModule_affineSection_isIso_of_regularPrincipal i U m hmreg hmprincipal,
      hmreg, hmprincipal⟩
  · have hxoff : x ∈ ({P.1} : Set N)ᶜ := hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUoff⟩ :=
      N.isBasis_affineOpens.exists_subset_of_mem_open hxoff P.2.isOpen_compl
    let UA : N.affineOpens := ⟨U, hU⟩
    have hPU : P.1 ∉ U := by
      intro h
      exact hUoff h (Set.mem_singleton P.1)
    obtain ⟨m, hm, hiso⟩ := closedPointIdeal_affine_unitGenerator_away N P UA hPU
    refine ⟨UA, hxU, m, hiso, ?_⟩
    rw [hm, closedPointIdeal_affine_eq_top_away N P UA hPU, Ideal.span_singleton_one]
    exact ⟨isRegular_one, rfl⟩

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- At EVERY point x of the SAME primitive normalization, the SAME ideal
has an ACTUAL affine rank-one chart. At P its regular equation comes from
the internally proved DVR; elsewhere its equation is 1 on the complement.
The original section-induced hom is the asserted isomorphism. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
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
      ∃ U : N.affineOpens, x ∈ U.1 ∧ ∃ m : M.val.presheaf.obj (op U.1),
        IsIso (schemeModuleSectionOnOpenHom M U.1 m) ∧
        let z : Γ(N, U.1) :=
          (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app (op U.1) m
        IsRegular z ∧ i.ker.ideal U = Ideal.span ({z} : Set Γ(N, U.1)) := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P x
  exact closedPointIdeal_rankOne_chart_of_regularGenerator N P
    (projectiveIntersection_genericNormalization_closedPoint_ideal_affine_regularGenerator
      p q hp hp0 n hn hq hnot P) x

/-- Genuine primitive global local-freeness of the SAME point ideal, from
the actual rank-one charts above. Every chart has exactly ONE generator;
this statement never uses a supplied free cover or invertibility premise. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ideal_isLocallyFree
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      (IdealSheafDataModule.closedImmersionModule i).IsLocallyFree := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from IdealSheafDataModule.closedImmersionModule i)
  have hc := projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
    p q hp hp0 n hn hq hnot P
  let U : N → N.affineOpens := fun x => Classical.choose (hc x)
  have hU (x : N) : x ∈ (U x).1 := (Classical.choose_spec (hc x)).1
  let m (x : N) : M.val.presheaf.obj (op (U x).1) :=
    Classical.choose ((Classical.choose_spec (hc x)).2)
  have hm (x : N) : IsIso (schemeModuleSectionOnOpenHom M (U x).1 (m x)) :=
    (Classical.choose_spec ((Classical.choose_spec (hc x)).2)).1
  apply sheaf_isLocallyFree_of_pointwise_free N M (fun x => (U x).1) hU
    (fun _ => PUnit.{u+1})
  intro x
  letI := hm x
  let e : SheafOfModules.unit ((U x).1 : Scheme.{u}).ringCatSheaf ≅
      M.restrict (U x).1.ι := asIso (schemeModuleSectionOnOpenHom M (U x).1 (m x))
  let eOver := ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit (U x).1 e.symm
  exact (coproductUniqueIso (fun _ : PUnit.{u+1} =>
    SheafOfModules.unit (N.ringCatSheaf.over (U x).1))) ≪≫ eOver.symm

end PfaffianDescent.Coray
