import AtlasCut

namespace CutWords1150
open AtlasLower AtlasMemo
set_option maxRecDepth 14000
set_option maxHeartbeats 9500000

def s40 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]

private def z40c0 : State := [0xc183060c1830600000000000000, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e0 : optimized 6 0 z40c0 = false := by decide +kernel

private def z40c1 : State := [0xc183060c1830601fff8001fff80, 0x1020408102040800000000000000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e1 : optimized 6 0 z40c1 = false := by decide +kernel

private def z40c2 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x8102040810204000000000000000, 0xa142850a1428500000000000007f]
private theorem e2 : optimized 6 0 z40c2 = false := by decide +kernel

private def z40c3 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xbf7efdfbf7efdf0000000000007f]
private theorem e3 : optimized 6 0 z40c3 = false := by decide +kernel

private def z40c4 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x8d1a3468d1a346fffffff01fff80, 0xa142850a1428500000000000007f]
private theorem e4 : optimized 6 0 z40c4 = false := by decide +kernel

private def z40c5 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x91224489122448ffffffffe00000, 0xa142850a1428500000000000007f]
private theorem e5 : optimized 6 0 z40c5 = false := by decide +kernel

private def z40c6 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e6 : optimized 6 0 z40c6 = false := by decide +kernel

private def z40c7 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xe1c3870e1c3870ffffffffffff80]
private theorem e7 : optimized 6 0 z40c7 = false := by decide +kernel

private def z40c8 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x6cd9b366cd9b3601fff80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e8 : optimized 6 0 z40c8 = false := by decide +kernel

private def z40c9 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x70e1c3870e1c38fe00000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e9 : optimized 6 0 z40c9 = false := by decide +kernel

private def z40c10 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e10 : optimized 6 0 z40c10 = false := by decide +kernel

private def z40c11 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e11 : optimized 6 1 z40c11 = false := by decide +kernel

private def z40c12 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f, 0xbf7efdfbf7efdf0000000000007f]
private theorem e12 : optimized 6 0 z40c12 = false := by decide +kernel

private def z40c13 : State := [0xc183060c1830601fff8001fff80, 0x10204081020408fe00000fe00000, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xbf7efdfbf7efdf0000000000007f]
private theorem e13 : optimized 6 1 z40c13 = false := by decide +kernel

private def z40c14 : State := [0xc183060c1830601fff8001fff80, 0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e14 : optimized 6 0 z40c14 = false := by decide +kernel

private def z40c15 : State := [0xc183060c1830601fff8001fff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x52a54a952a54a9fe0007ffe00000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e15 : optimized 6 0 z40c15 = false := by decide +kernel

private def z40c16 : State := [0xc183060c1830601fff8001fff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x70e1c3870e1c38fe00000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e16 : optimized 6 0 z40c16 = false := by decide +kernel

private def z40c17 : State := [0xc183060c1830601fff8001fff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0x91224489122448ffffffffe00000, 0xa142850a1428500000000000007f]
private theorem e17 : optimized 6 0 z40c17 = false := by decide +kernel

private def z40c18 : State := [0xc183060c1830601fff8001fff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x91224489122448ffffffffe00000, 0xa142850a1428500000000000007f]
private theorem e18 : optimized 6 1 z40c18 = false := by decide +kernel

private def z40c19 : State := [0xc183060c1830601fff8001fff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x70e1c3870e1c38fe00000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e19 : optimized 6 1 z40c19 = false := by decide +kernel

private def z40c20 : State := [0x10204081020408fe00000fe00000, 0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e20 : optimized 6 0 z40c20 = false := by decide +kernel

private def z40c21 : State := [0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x4e9d3a74e9d3a701fffff01fff80, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e21 : optimized 6 0 z40c21 = false := by decide +kernel

private def z40c22 : State := [0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x6cd9b366cd9b3601fff80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e22 : optimized 6 0 z40c22 = false := by decide +kernel

private def z40c23 : State := [0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0x8d1a3468d1a346fffffff01fff80, 0xa142850a1428500000000000007f]
private theorem e23 : optimized 6 0 z40c23 = false := by decide +kernel

private def z40c24 : State := [0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x8d1a3468d1a346fffffff01fff80, 0xa142850a1428500000000000007f]
private theorem e24 : optimized 6 1 z40c24 = false := by decide +kernel

private def z40c25 : State := [0x10204081020408fe00000fe00000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x6cd9b366cd9b3601fff80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e25 : optimized 6 1 z40c25 = false := by decide +kernel

private def z40c26 : State := [0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e26 : optimized 6 1 z40c26 = false := by decide +kernel

private def next : Layer := #[z40c0,z40c1,z40c2,z40c3,z40c4,z40c5,z40c6,z40c7,z40c8,z40c9,z40c10,z40c11,z40c12,z40c13,z40c14,z40c15,z40c16,z40c17,z40c18,z40c19,z40c20,z40c21,z40c22,z40c23,z40c24,z40c25,z40c26]
private theorem afterStep : AtlasCut.Anchors 6 next := by
  intro s mem nd
  simp only [next, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact AtlasCut.leaf e0 nd
  · exact AtlasCut.leaf e1 nd
  · exact AtlasCut.leaf e2 nd
  · exact AtlasCut.leaf e3 nd
  · exact AtlasCut.leaf e4 nd
  · exact AtlasCut.leaf e5 nd
  · exact AtlasCut.leaf e6 nd
  · exact AtlasCut.leaf e7 nd
  · exact AtlasCut.leaf e8 nd
  · exact AtlasCut.leaf e9 nd
  · exact AtlasCut.leaf e10 nd
  · exact AtlasCut.leaf e11 nd
  · exact AtlasCut.leaf e12 nd
  · exact AtlasCut.leaf e13 nd
  · exact AtlasCut.leaf e14 nd
  · exact AtlasCut.leaf e15 nd
  · exact AtlasCut.leaf e16 nd
  · exact AtlasCut.leaf e17 nd
  · exact AtlasCut.leaf e18 nd
  · exact AtlasCut.leaf e19 nd
  · exact AtlasCut.leaf e20 nd
  · exact AtlasCut.leaf e21 nd
  · exact AtlasCut.leaf e22 nd
  · exact AtlasCut.leaf e23 nd
  · exact AtlasCut.leaf e24 nd
  · exact AtlasCut.leaf e25 nd
  · exact AtlasCut.leaf e26 nd
private theorem completeStep : (#[s40] : Layer).all (stateOK next 7) = true := by decide +kernel
theorem node40 : s40.Nodup → ¬ live basicOps goal 7 s40.toFinset :=
  (AtlasCut.step afterStep completeStep) s40 (by simp)

end CutWords1150
