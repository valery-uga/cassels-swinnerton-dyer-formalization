import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffinePair
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffineParameterFibre
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Actual affine finite pair zeros are flat at a regular curve parameter -/
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_nativeAffine_pair_zero_stalk_flat
    {C B : Type u} [CommRing C] [CommRing B] [IsNoetherianRing B]
    (g : C →+* B) [Flat (Spec.map (CommRingCat.ofHom g))]
    (a b : B)
    [LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span ({a, b} : Set B)))) ≫ Spec.map (CommRingCat.ofHom g))]
    (z : Spec (.of (B ⧸ Ideal.span ({a, b} : Set B))))
    [((Spec.map (CommRingCat.ofHom g))
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))) z)).asIdeal.IsMaximal]
    [IsRegularLocalRing ((Spec (.of C)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom g))
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))) z)))]
    (hdR : ringKrullDim ((Spec (.of C)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom g))
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))) z))) = 1)
    (t : C) (ht : ((Spec.map (CommRingCat.ofHom g))
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))) z)).asIdeal =
        Ideal.span {t})
    [IsRegularLocalRing (((Spec.map (CommRingCat.ofHom g)).fiber
      ((Spec.map (CommRingCat.ofHom g))
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))) z))).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom g)).asFiber
            ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))) z)))]
    (hdF : ringKrullDim (((Spec.map (CommRingCat.ofHom g)).fiber
      ((Spec.map (CommRingCat.ofHom g))
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))) z))).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom g)).asFiber
            ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B))))) z))) = 2) :
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({a, b} : Set B)))) ≫
      Spec.map (CommRingCat.ofHom g)).stalkMap z).hom.Flat := by
  let I := Ideal.span ({a, b} : Set B)
  let q := Ideal.Quotient.mk I
  let i := Spec.map (CommRingCat.ofHom q)
  let f := Spec.map (CommRingCat.ofHom g)
  let x := i z
  let y := f x
  let R := (Spec (.of C)).presheaf.stalk y
  let A := (Spec (.of B)).presheaf.stalk x
  let D := (Spec (.of (B ⧸ I))).presheaf.stalk z
  let π : R := (Spec (.of C)).presheaf.germ ⊤ y (by trivial)
    ((Scheme.ΓSpecIso (.of C)).inv t)
  let aa : A := (Spec (.of B)).presheaf.germ ⊤ x (by trivial)
    ((Scheme.ΓSpecIso (.of B)).inv a)
  let bb : A := (Spec (.of B)).presheaf.germ ⊤ x (by trivial)
    ((Scheme.ΓSpecIso (.of B)).inv b)
  let r := (f.stalkMap x).hom
  let s := (i.stalkMap z).hom
  letI : Algebra R A := r.toAlgebra
  letI : IsLocalHom (algebraMap R A) := f.toLRSHom.prop x
  letI : Module.Flat R A := Flat.stalkMap f x
  letI : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hk : RingHom.ker s = Ideal.span ({aa, bb} : Set A) :=
    cubicClosedPointSerreFiniteZeroResidual_spec_pairZero_stalkMap_kernel a b z
  have hm : Ideal.span ({aa, bb} : Set A) ≤ maximalIdeal A := by
    rw [← hk]
    exact le_maximalIdeal (RingHom.ker_ne_top s)
  have hπ : maximalIdeal R = Ideal.span {π} :=
    cubicClosedPointSerreFiniteZeroResidual_spec_parameter_generates_maximalIdeal y t ht
  have hfibre := cubicClosedPointSerreFiniteZeroResidual_nativeAffine_parameter_quotient_regular_dim_two
    g x t ht hdF
  letI : IsRegularLocalRing (A ⧸ Ideal.span {algebraMap R A π}) := hfibre.1
  have hdA : ringKrullDim (A ⧸ Ideal.span {algebraMap R A π}) = 2 := hfibre.2
  let gD := q.comp g
  have hcomp : Spec.map (CommRingCat.ofHom gD) = i ≫ f := by
    change Spec.map ((CommRingCat.ofHom g) ≫ (CommRingCat.ofHom q)) = _
    rw [Spec.map_comp]
  have hy : (Spec.map (CommRingCat.ofHom gD)) z = y := by rw [hcomp]; rfl
  letI : ((Spec.map (CommRingCat.ofHom gD)) z).asIdeal.IsMaximal := by rw [hy]; infer_instance
  letI : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom gD)) := by rw [hcomp]; infer_instance
  have hsource := cubicClosedPointSerreFiniteZeroResidual_nativeAffine_parameter_quotient_artinian
    gD z t (by rw [hy]; exact ht)
  rw [hcomp] at hsource
  change IsArtinianRing (D ⧸ Ideal.span {((i ≫ f).stalkMap z).hom π}) at hsource
  rw [Scheme.Hom.stalkMap_comp] at hsource
  have hArt : IsArtinianRing (D ⧸ Ideal.span {s (algebraMap R A π)}) := by
    exact hsource
  letI := hArt
  letI : IsArtinianRing ((A ⧸ Ideal.span {algebraMap R A π}) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.span {algebraMap R A π}) aa,
        Ideal.Quotient.mk (Ideal.span {algebraMap R A π}) bb} :
        Set (A ⧸ Ideal.span {algebraMap R A π}))) :=
    cubicClosedPointSerreFiniteZeroResidual_artinian_fibre_pair_of_zero_parameter_quotient
      s (i.stalkMap_surjective z) aa bb (algebraMap R A π) hk
  letI : Module.Flat R (A ⧸ Ideal.span ({aa, bb} : Set A)) :=
    cubicClosedPointSerreFiniteZeroResidual_pair_quotient_flat_of_regular_surface_fibre
      R hdR π hπ A hdA aa bb (hm (Ideal.subset_span (by simp)))
        (hm (Ideal.subset_span (by simp)))
  have hquot : ((Ideal.Quotient.mk (Ideal.span ({aa, bb} : Set A))).comp r).Flat := by
    change (algebraMap R (A ⧸ Ideal.span ({aa, bb} : Set A))).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflat := cubicClosedPointSerreFiniteZeroResidual_flat_comp_of_flat_quotient
    r s (i.stalkMap_surjective z) _ hk hquot
  rw [Scheme.Hom.stalkMap_comp]
  exact hflat

end PfaffianDescent
