import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part0
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part1
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part2
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part3
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part4
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part5
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part6
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part7
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part8
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part9
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part10
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part11
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part12
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part13
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part14
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part15
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part16
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part17
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part18
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part19
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part20
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part21
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part22
import Airbender.Proofs.GKRProtocol.ROMParts.Unified.Column6.Part23
import Airbender.Import.GKRProtocol.BlockCoverageImport
import Airbender.Proofs.GKRProtocol.ColumnSlices
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.ROMColumns.Unified.Column6
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part selected from Data.GKRSetup.Unified.setupColumn6 start 24285 stop 24287
column_blocks_part back from Data.GKRSetup.Unified.setupColumn6 start 24287 stop 24289

column_parts_cover sourceCoverage from Data.GKRSetup.Unified.setupColumn6 parts [front0, front1, front2, front3, front4, front5, front6, front7, front8, front9, front10, front11, front12, front13, front14, front15, front16, front17, front18, front19, front20, front21, front22, front23, front24, front25, front26, front27, front28, front29, front30, front31, front32, front33, front34, front35, front36, front37, front38, front39, front40, front41, front42, front43, front44, front45, front46, front47, front48, front49, front50, front51, front52, front53, front54, front55, front56, front57, front58, front59, front60, front61, front62, front63, front64, front65, front66, front67, front68, front69, front70, front71, front72, front73, front74, front75, front76, front77, front78, front79, front80, front81, front82, front83, front84, front85, front86, front87, front88, front89, front90, front91, front92, front93, front94, front95, front96, front97, front98, front99, front100, front101, front102, front103, front104, front105, front106, front107, front108, front109, front110, front111, front112, front113, front114, front115, front116, front117, front118, front119, front120, front121, front122, front123, front124, front125, front126, front127, front128, front129, front130, front131, front132, front133, front134, front135, front136, front137, front138, front139, front140, front141, front142, front143, front144, front145, front146, front147, front148, front149, front150, front151, front152, front153, front154, front155, front156, front157, front158, front159, front160, front161, front162, front163, front164, front165, front166, front167, front168, front169, front170, front171, front172, front173, front174, front175, front176, front177, front178, front179, front180, front181, front182, front183, front184, front185, front186, front187, front188, front189, selected, back]

noncomputable def front : List Setup.Block := ([front0, front1, front2, front3, front4, front5, front6, front7, front8, front9, front10, front11, front12, front13, front14, front15, front16, front17, front18, front19, front20, front21, front22, front23, front24, front25, front26, front27, front28, front29, front30, front31, front32, front33, front34, front35, front36, front37, front38, front39, front40, front41, front42, front43, front44, front45, front46, front47, front48, front49, front50, front51, front52, front53, front54, front55, front56, front57, front58, front59, front60, front61, front62, front63, front64, front65, front66, front67, front68, front69, front70, front71, front72, front73, front74, front75, front76, front77, front78, front79, front80, front81, front82, front83, front84, front85, front86, front87, front88, front89, front90, front91, front92, front93, front94, front95, front96, front97, front98, front99, front100, front101, front102, front103, front104, front105, front106, front107, front108, front109, front110, front111, front112, front113, front114, front115, front116, front117, front118, front119, front120, front121, front122, front123, front124, front125, front126, front127, front128, front129, front130, front131, front132, front133, front134, front135, front136, front137, front138, front139, front140, front141, front142, front143, front144, front145, front146, front147, front148, front149, front150, front151, front152, front153, front154, front155, front156, front157, front158, front159, front160, front161, front162, front163, front164, front165, front166, front167, front168, front169, front170, front171, front172, front173, front174, front175, front176, front177, front178, front179, front180, front181, front182, front183, front184, front185, front186, front187, front188, front189] : List (List Setup.Block)).flatten

noncomputable def selectedColumn : Setup.Column := ⟨selected.toArray⟩

theorem prefixLength : (front.map Setup.Block.length).sum = 589948 := by
  simp only [front, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, frontLength0, frontLength1, frontLength2, frontLength3, frontLength4, frontLength5, frontLength6, frontLength7, frontLength8, frontLength9, frontLength10, frontLength11, frontLength12, frontLength13, frontLength14, frontLength15, frontLength16, frontLength17, frontLength18, frontLength19, frontLength20, frontLength21, frontLength22, frontLength23, frontLength24, frontLength25, frontLength26, frontLength27, frontLength28, frontLength29, frontLength30, frontLength31, frontLength32, frontLength33, frontLength34, frontLength35, frontLength36, frontLength37, frontLength38, frontLength39, frontLength40, frontLength41, frontLength42, frontLength43, frontLength44, frontLength45, frontLength46, frontLength47, frontLength48, frontLength49, frontLength50, frontLength51, frontLength52, frontLength53, frontLength54, frontLength55, frontLength56, frontLength57, frontLength58, frontLength59, frontLength60, frontLength61, frontLength62, frontLength63, frontLength64, frontLength65, frontLength66, frontLength67, frontLength68, frontLength69, frontLength70, frontLength71, frontLength72, frontLength73, frontLength74, frontLength75, frontLength76, frontLength77, frontLength78, frontLength79, frontLength80, frontLength81, frontLength82, frontLength83, frontLength84, frontLength85, frontLength86, frontLength87, frontLength88, frontLength89, frontLength90, frontLength91, frontLength92, frontLength93, frontLength94, frontLength95, frontLength96, frontLength97, frontLength98, frontLength99, frontLength100, frontLength101, frontLength102, frontLength103, frontLength104, frontLength105, frontLength106, frontLength107, frontLength108, frontLength109, frontLength110, frontLength111, frontLength112, frontLength113, frontLength114, frontLength115, frontLength116, frontLength117, frontLength118, frontLength119, frontLength120, frontLength121, frontLength122, frontLength123, frontLength124, frontLength125, frontLength126, frontLength127, frontLength128, frontLength129, frontLength130, frontLength131, frontLength132, frontLength133, frontLength134, frontLength135, frontLength136, frontLength137, frontLength138, frontLength139, frontLength140, frontLength141, frontLength142, frontLength143, frontLength144, frontLength145, frontLength146, frontLength147, frontLength148, frontLength149, frontLength150, frontLength151, frontLength152, frontLength153, frontLength154, frontLength155, frontLength156, frontLength157, frontLength158, frontLength159, frontLength160, frontLength161, frontLength162, frontLength163, frontLength164, frontLength165, frontLength166, frontLength167, frontLength168, frontLength169, frontLength170, frontLength171, frontLength172, frontLength173, frontLength174, frontLength175, frontLength176, frontLength177, frontLength178, frontLength179, frontLength180, frontLength181, frontLength182, frontLength183, frontLength184, frontLength185, frontLength186, frontLength187, frontLength188, frontLength189]
  decide +kernel

theorem selectedLength : (selectedColumn.blocks.toList.map Setup.Block.length).sum = 1507593 := by decide +kernel

theorem sourceShape : Data.GKRSetup.Unified.setupColumn6.blocks.toList = front ++ (selectedColumn.blocks.toList ++ back) := by
  rw [sourceCoverage]
  simp only [front, selectedColumn, List.toList_toArray, List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]

theorem column_value (index : Fin 1048576) :
    Data.GKRSetup.Unified.setupColumn6.get? (590081 + index.val) = selectedColumn.get? (133 + index.val) := by
  have actual := column_slice_value Data.GKRSetup.Unified.setupColumn6 selectedColumn front back 589948 1507593
    sourceShape prefixLength selectedLength (133 + index.val) (by have := index.isLt; omega)
  simpa only [show 589948 + (133 + index.val) = 590081 + index.val by omega] using actual

end Airbender.Compiler.ROMColumns.Unified.Column6
