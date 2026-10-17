import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProductRankTransport
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProductChartMaps

/-! # Small equation transport between the actual chart structure maps -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceRankProductCompRow
    {K : Type u} [CommRing K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n)
    (A : Matrix (Fin 6) (Fin n) Γ(B, ⊤)) (r : Fin 6) :
    Γ(pullback b (chartι (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)) j ≫ toBase _), ⊤) :=
  ∑ k : Fin n,
    (pullback.snd b (chartι (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)) j ≫ toBase _)).appTop
      ((Scheme.ΓSpecIso (.of (ChartRing (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin n) K)) j))).inv
          (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j k)) *
    (pullback.fst b (chartι (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)) j ≫ toBase _)).appTop (A r k)

def serreIncidenceRankChartStructureIso
    {K : Type u} [CommRing K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n) :
    pullback b (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j ≫ toBase _) ≅
    pullback b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j))) :=
  pullback.congrHom rfl (chartι_toBase _ j)

@[reassoc]
lemma serreIncidenceRankChartStructureIso_inv_fst
    {K : Type u} [CommRing K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n) :
    (serreIncidenceRankChartStructureIso b j).inv ≫ pullback.fst b
      (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j ≫ toBase _) =
    pullback.fst b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j))) := by
  simp [serreIncidenceRankChartStructureIso, pullback.congrHom, pullback.map]

@[reassoc]
lemma serreIncidenceRankChartStructureIso_inv_snd
    {K : Type u} [CommRing K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n) :
    (serreIncidenceRankChartStructureIso b j).inv ≫ pullback.snd b
      (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j ≫ toBase _) =
    pullback.snd b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j))) := by
  simp [serreIncidenceRankChartStructureIso, pullback.congrHom, pullback.map]

lemma serreIncidenceRankChartStructureIso_toProduct
    {K : Type u} [CommRing K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n) :
    (serreIncidenceRankChartStructureIso b j).inv ≫
      serreIncidenceProductChartToProduct b
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) (chartι _ j) =
    serreIncidenceRankProductChart b j := by
  apply pullback.hom_ext
  · rw [Category.assoc, serreIncidenceProductChartToProduct_fst]
    exact (serreIncidenceRankChartStructureIso_inv_fst b j).trans
      (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, serreIncidenceProductChartToProduct_snd,
      ← Category.assoc, serreIncidenceRankChartStructureIso_inv_snd]
    exact (pullback.lift_snd _ _ _).symm

lemma serreIncidenceΓFunction_transport
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (he : f ≫ g = h) (a : Γ(Z, ⊤)) : f.appTop (g.appTop a) = h.appTop a := by
  have hh := congrArg (fun q => q.appTop) he
  rw [Scheme.Hom.comp_appTop] at hh
  exact congrArg (fun q => q a) hh

lemma serreIncidenceProductRow_transport
    {R S : Type u} [CommRing R] [CommRing S] {ι : Type*} [Fintype ι]
    (f : R →+* S) (c a : ι → R) (c' a' : ι → S)
    (hc : ∀ k, f (c k) = c' k) (ha : ∀ k, f (a k) = a' k) :
    f (∑ k, c k * a k) = ∑ k, c' k * a' k := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul, hc k, ha k]

lemma serreIncidenceRankChartStructureIso_row
    {K : Type u} [CommRing K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n)
    (A : Matrix (Fin 6) (Fin n) Γ(B, ⊤)) (r : Fin 6) :
    (serreIncidenceRankChartStructureIso b j).inv.appTop
      (serreIncidenceRankProductCompRow b j A r) = serreIncidenceRankProductRow b j A r := by
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin n) K) := ⊥
  let q := chartι J j ≫ toBase J
  let q' := Spec.map (CommRingCat.ofHom (chartBaseMap J j))
  let e := serreIncidenceRankChartStructureIso b j
  exact serreIncidenceProductRow_transport e.inv.appTop.hom
    (fun k => (pullback.snd b q).appTop
      ((Scheme.ΓSpecIso (.of (ChartRing J j))).inv (chartCoordinate J j k)))
    (fun k => (pullback.fst b q).appTop (A r k))
    (fun k => (pullback.snd b q').appTop
      ((Scheme.ΓSpecIso (.of (ChartRing J j))).inv (chartCoordinate J j k)))
    (fun k => (pullback.fst b q').appTop (A r k))
    (fun k => serreIncidenceΓFunction_transport e.inv _ _
      (serreIncidenceRankChartStructureIso_inv_snd b j) _)
    (fun k => serreIncidenceΓFunction_transport e.inv _ _
      (serreIncidenceRankChartStructureIso_inv_fst b j) _)

theorem serreIncidenceRankProductEquations_spec
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n)
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin n) Γ(B, ⊤))
    (h : I.comap (serreIncidenceProductChartToProduct b
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
      (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j)) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceRankProductCompRow b j A)))) :
    I.comap (serreIncidenceRankProductChart b j) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceRankProductRow b j A))) := by
  let e := serreIncidenceRankChartStructureIso b j
  have hh := congrArg (fun P => P.comap e.inv) h
  rw [← Scheme.IdealSheafData.comap_comp, serreIncidenceRankChartStructureIso_toProduct] at hh
  have h2 := cubicClosedPointSerreFiniteZeroResidual_affineIdeal_comap e.inv
    (Ideal.span (Set.range (serreIncidenceRankProductCompRow b j A)))
  have h3 := serreIncidenceSpan_map_range e.inv.appTop.hom
    (serreIncidenceRankProductCompRow b j A) (serreIncidenceRankProductRow b j A)
    (fun r => serreIncidenceRankChartStructureIso_row b j A r)
  exact hh.trans (h2.trans (congrArg Scheme.IdealSheafData.ofIdealTop h3))

end PfaffianDescent
