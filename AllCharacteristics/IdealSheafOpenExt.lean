import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Equality and restriction of ideal sheaves on open covers

Equality can be checked on actual affine-open pullbacks. Kernel ideal sheaves
of quasi-compact maps commute with open base change. These statements retain
the original scheme morphisms and allow affine image calculations to glue.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics
universe u

/-- Equality after restriction to an affine open gives equality of the
original ideals of sections on that open. -/
lemma ideal_eq_of_comap_open {X : Scheme.{u}} {I J : X.IdealSheafData}
    (U : X.affineOpens) (h : I.comap U.1.ι = J.comap U.1.ι) : I.ideal U = J.ideal U := by
  have : IsAffine U.1.toScheme := U.2
  have he := congrArg (fun K : U.1.toScheme.IdealSheafData =>
    K.ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩) h
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at he
  have hi := Ideal.comap_injective_of_surjective (U.1.ι.appIso ⊤).inv.hom
    (ConcreteCategory.bijective_of_isIso (U.1.ι.appIso ⊤).inv).surjective he
  have heU : (⟨U.1.ι ''ᵁ ⊤,
      (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩ : X.affineOpens) = U :=
    Subtype.ext U.1.ι_image_top
  exact (congrArg (fun V : X.affineOpens => I.ideal V = J.ideal V) heU).mp hi

/-- Ideal sheaves agree if their pullbacks to a covering family of actual
affine opens agree. -/
lemma idealSheaf_ext_of_comap_affine_cover {X : Scheme.{u}} {I J : X.IdealSheafData}
    {ι : Type*} (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (h : ∀ i, I.comap (U i).1.ι = J.comap (U i).1.ι) : I = J :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top U hU (fun i => ideal_eq_of_comap_open (U i) (h i))

/-- Kernel ideal sheaves of quasi-compact morphisms commute with open base change. -/
lemma kernel_of_open_pullback
    {P X Y U : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ U}
    {i : X ⟶ Y} {j : U ⟶ Y} [QuasiCompact i] [IsOpenImmersion j]
    (h : IsPullback a b i j) : b.ker = i.ker.comap j := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i b a j h.flip V,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

/-- The kernel ideal of a local closed subscheme viewed in the ambient scheme
through an open immersion. -/
noncomputable def openKernelExtension
    {X U : Scheme.{u}} (I : U.IdealSheafData) (j : U ⟶ X) : X.IdealSheafData :=
  (I.subschemeι ≫ j).ker

/-- Extending an ideal-defined closed subscheme through a quasi-compact open
immersion and taking its kernel ideal restricts back to the original ideal.
This is the local extension calculation used when compatible zero ideals are
assembled from affine charts. -/
theorem idealSheafData_comap_ker_subscheme_comp_open
    {X U : Scheme.{u}} (I : U.IdealSheafData) (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact (I.subschemeι ≫ j)] :
    (openKernelExtension I j).comap j = I := by
  have hRange : Set.range (I.subschemeι ≫ j) ⊆ Set.range j := by
    rintro x ⟨y, rfl⟩
    exact ⟨I.subschemeι y, rfl⟩
  let l : I.subscheme ⟶ U :=
    IsOpenImmersion.lift j (I.subschemeι ≫ j) hRange
  have hl : l = I.subschemeι := by
    apply (cancel_mono j).1
    simp [l]
  have hker : l.ker = (I.subschemeι ≫ j).ker.comap j :=
    kernel_of_open_pullback
    (IsOpenImmersion.isPullback_lift_id (I.subschemeι ≫ j)
      j hRange).flip
  rw [hl] at hker
  exact hker.symm.trans I.ker_subschemeι

/-- For an affine open in a quasi-separated scheme, the quasi-compactness
needed by `idealSheafData_comap_ker_subscheme_comp_open` is automatic. -/
theorem idealSheafData_comap_ker_subscheme_comp_open_of_isAffine
    {X U : Scheme.{u}} (I : U.IdealSheafData) (j : U ⟶ X)
    [IsOpenImmersion j] [IsAffine U] [QuasiSeparatedSpace X] :
    (I.subschemeι ≫ j).ker.comap j = I := by
  let _ : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  let _ : CompactSpace I.subscheme := inferInstance
  let _ : QuasiCompact (I.subschemeι ≫ j) := inferInstance
  exact idealSheafData_comap_ker_subscheme_comp_open I j

end AllCharacteristics
