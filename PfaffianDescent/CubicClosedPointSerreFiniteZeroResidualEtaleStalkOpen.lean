import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeEtaleOpen
import Mathlib.RingTheory.Etale.Locus

noncomputable section
open AlgebraicGeometry CategoryTheory RingHom
namespace PfaffianDescent
universe u
variable {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false

lemma cubicClosedPointSerreFiniteZeroResidual_formallyEtale_iff
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) :
    f.FormallyEtale ↔ f.FormallyUnramified ∧ f.FormallySmooth := by
  letI := f.toAlgebra
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth

lemma cubicClosedPointSerreFiniteZeroResidual_formallyEtale_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
      (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyEtale ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.etaleLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [cubicClosedPointSerreFiniteZeroResidual_formallyEtale_iff,
      Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth,
      ← formallyUnramified_algebraMap, ← formallySmooth_algebraMap]
    exact and_congr
      (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx))
      (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
        (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx))
  · exact Algebra.FormallyEtale.iff_restrictScalars.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma cubicClosedPointSerreFiniteZeroResidual_exists_etale_of_formallyEtale_stalk
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U),
      x ∈ V ∧ (f.appLE U V hVU).hom.Etale := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsEtaleAt _ _ := (cubicClosedPointSerreFiniteZeroResidual_formallyEtale_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.etale_algebraMap] at hr
    convert!
      RingHom.Etale.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]

theorem cubicClosedPointSerreFiniteZeroResidual_mem_etaleOpen_of_formallyEtale_stalk
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    x ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen f := by
  obtain ⟨U, hU, V, hV, hVU, hxV, he⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_exists_etale_of_formallyEtale_stalk f x H
  letI : IsAffine (U : Scheme) := hU
  letI : IsAffine (V : Scheme) := hV
  have he' : ((f.resLE U V hVU).appTop).hom.Etale :=
    (RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U V hVU)).mpr he
  letI : Etale (f.resLE U V hVU) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mpr he'
  letI : Etale (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hVU]
    infer_instance
  exact (cubicClosedPointSerreFiniteZeroResidual_le_etaleOpen f V) hxV

end PfaffianDescent
