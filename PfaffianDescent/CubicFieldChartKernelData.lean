import PfaffianDescent.CubicElevenPointCanonicalChartKernel

/-! A field-valued output proposition for the actual cubic chart restriction
kernel. The constructor only packages its literal witnesses; native existence
is proved separately from the original smooth cubic. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def CubicFieldChartKernelData
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP) : Prop :=
    ∃ (E : Type u) (_ : Field E) (β : F →+* E),
    letI : Algebra F E := β.toAlgebra
    ∃ (j : Fin 4) (g : ChartRing (equationIdeal P hP) j →+* L)
      (α : Fin 11 → (L →ₐ[F] E))
      (y : Fin 11 → Fin 4 → E) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E),
      g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i ∧
      (∀ k, y k j ≠ 0) ∧
      (∀ k r, α k (g (linearChartCoordinate (equationIdeal P hP)
          (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) r)) =
        (y k j)⁻¹ * y k r) ∧
      (∀ k, aeval (y k) (P.map β) = 0) ∧
      (∀ k r, (J k r).fst = y (k.castAdd 8) r) ∧
      (∀ k, aeval (J k) (P.map β) = 0) ∧
      Function.Surjective (cubicElevenPointFullJetRestriction y J) ∧
      let R := cubicHomogeneousChartRestriction (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g
      (∀ q, R q = 0 → cubicElevenPointValueRestriction y
        (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0) ∧
      Function.Surjective R ∧
      finrank F R.ker = 9 ∧
      ∀ B : Basis (Fin 9) F R.ker,
        Submodule.span E (Set.range (fun k : Fin 9 => fun r : Fin 3 =>
          (aeval (J r) ((B k).1.1.map (algebraMap F E))).snd)) = ⊤

theorem cubicFieldChartKernelData_of_witnesses
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface P hP)
    (β : F →+* E)
    (j : Fin 4) (g : ChartRing (equationIdeal P hP) j →+* L)
    (α : Fin 11 → (letI : Algebra F E := β.toAlgebra; L →ₐ[F] E))
    (y : Fin 11 → Fin 4 → E) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hgb : g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L)
    (hgi : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i)
    (hnz : ∀ k, y k j ≠ 0)
    (hcoords : ∀ k r, α k (g (linearChartCoordinate (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) r)) =
      (y k j)⁻¹ * y k r)
    (hvalues : ∀ k, aeval (y k) (P.map β) = 0)
    (hresidue : ∀ k r, (J k r).fst = y (k.castAdd 8) r)
    (hJp : ∀ k, aeval (J k) (P.map β) = 0)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction y J))
    (hmem : letI : Algebra F E := β.toAlgebra;
      let R := cubicHomogeneousChartRestriction (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g;
      ∀ q, R q = 0 → cubicElevenPointValueRestriction y
        (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0)
    (honto : Function.Surjective (cubicHomogeneousChartRestriction (equationIdeal P hP)
      (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g))
    (hdim : finrank F (cubicHomogeneousChartRestriction (equationIdeal P hP)
      (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g).ker = 9)
    (hspan : letI : Algebra F E := β.toAlgebra;
      let R := cubicHomogeneousChartRestriction (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g;
      ∀ B : Basis (Fin 9) F R.ker,
        Submodule.span E (Set.range (fun k : Fin 9 => fun r : Fin 3 =>
          (aeval (J r) ((B k).1.1.map (algebraMap F E))).snd)) = ⊤) :
    CubicFieldChartKernelData P hP i :=
  ⟨E, inferInstance, β, j, g, α, y, J, hgb, hgi, hnz, hcoords,
    hvalues, hresidue, hJp, hfull, hmem, honto, hdim, hspan⟩

end PfaffianDescent
