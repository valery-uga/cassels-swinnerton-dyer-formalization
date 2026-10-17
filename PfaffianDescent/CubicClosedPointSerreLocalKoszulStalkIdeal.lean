import PfaffianDescent.CubicClosedPointSerreLocalKoszulStalk

/-! # Constructing the actual ideal-stalk coordinate from the Koszul row -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem cubicClosedPointSerreLocalKoszul_exists_idealCoordinate_of_composite
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (f g : R)
    (q : ModuleCat.of R (R × R) ⟶ M)
    (m : M ⟶ ModuleCat.of R R) [Epi q] [Mono m]
    (hcomp : q ≫ m = ModuleCat.ofHom (twoGeneratorLast f g)) :
    ∃ a : M ≅ ModuleCat.of R (Ideal.span ({f, g} : Set R)),
      a.hom ≫ ModuleCat.ofHom (Ideal.span ({f, g} : Set R)).subtype = m ∧
      q ≫ a.hom = ModuleCat.ofHom (localKoszulToIdeal f g) := by
  have hq : Function.Surjective q := (ModuleCat.epi_iff_surjective q).mp inferInstance
  have hm : Function.Injective m := (ModuleCat.mono_iff_injective m).mp inferInstance
  have hc : ∀ z, m (q z) = twoGeneratorLast f g z := fun z =>
    congrArg (fun k => k.hom z) hcomp
  have hmem (v : M) : m v ∈ Ideal.span ({f, g} : Set R) := by
    obtain ⟨z, rfl⟩ := hq v
    rw [hc]
    rw [← twoGeneratorLast_range]
    exact ⟨z, rfl⟩
  let l : M →ₗ[R] Ideal.span ({f, g} : Set R) :=
    m.hom.codRestrict _ hmem
  have hinj : Function.Injective l := by
    intro v w h
    exact hm (congrArg Subtype.val h)
  have hsurj : Function.Surjective l := by
    intro v
    have hv : (v : R) ∈ LinearMap.range (twoGeneratorLast f g) := by
      rw [twoGeneratorLast_range]
      exact v.2
    obtain ⟨z, hz⟩ := hv
    exact ⟨q z, Subtype.ext ((hc z).trans hz)⟩
  let a := (LinearEquiv.ofBijective l ⟨hinj, hsurj⟩).toModuleIso
  refine ⟨a, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change m (q z) = z.1 * f + z.2 * g
    have hz := hc z
    change m (q z) = f * z.1 + g * z.2 at hz
    simpa only [mul_comm] using hz

theorem cubicClosedPointSerreLocalKoszul_exists_idealCoordinate
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (U : X.Opens) (q f : Γ(X, U))
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (s : CubicClosedPointSerreLocalKoszulData i T U q f eT) (x : U) :
    ∃ a : (schemeModuleStalkModuleFunctor X (U.ι x)).obj (closedImmersionIdealTwist i T) ≅
      ModuleCat.of (X.presheaf.stalk (U.ι x))
        (Ideal.span ({X.presheaf.germ U (U.ι x) x.2 q,
          X.presheaf.germ U (U.ι x) x.2 f} : Set _)),
      a.hom ≫ ModuleCat.ofHom (Ideal.span ({X.presheaf.germ U (U.ι x) x.2 q,
        X.presheaf.germ U (U.ι x) x.2 f} : Set _)).subtype =
        cubicClosedPointSerreLocalKoszulIdealInclusionNative i T U eT x ∧
      (sectionRepresenterKoszulPairStalkIso X U (U.ι x) x.2).inv ≫
          cubicClosedPointSerreLocalKoszulLastNative i T U q f eT s x ≫ a.hom =
        ModuleCat.ofHom (localKoszulToIdeal (X.presheaf.germ U (U.ι x) x.2 q)
          (X.presheaf.germ U (U.ι x) x.2 f)) := by
  let q' := (sectionRepresenterKoszulPairStalkIso X U (U.ι x) x.2).inv ≫
    cubicClosedPointSerreLocalKoszulLastNative i T U q f eT s x
  let m := cubicClosedPointSerreLocalKoszulIdealInclusionNative i T U eT x
  letI := cubicClosedPointSerreLocalKoszulLastNative_epi i T U q f eT s x
  letI : Epi q' := by dsimp [q']; infer_instance
  letI : Mono m := cubicClosedPointSerreLocalKoszulIdealInclusionNative_mono i T U eT x
  obtain ⟨a, ha, hq⟩ := cubicClosedPointSerreLocalKoszul_exists_idealCoordinate_of_composite
    _ (X.presheaf.germ U (U.ι x) x.2 q) (X.presheaf.germ U (U.ι x) x.2 f)
    q' m (by
      simpa only [q', Category.assoc] using
        cubicClosedPointSerreLocalKoszulLastNative_coordinate i T U q f eT s x)
  exact ⟨a, ha, by simpa only [q', Category.assoc] using hq⟩

end PfaffianDescent
