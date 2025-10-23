import Lean
import AutograderLib

/-!
# Gradescope autograder for Lean

`AutograderLib` provided by <robertylewis/lean4-autograder-main>
-/

open Lean IO System Elab

def submissionUploadDir : FilePath := "/autograder/submission"
def resultsJsonPath : FilePath := ".." / "results" / "results.json"

/-! ### Core data structures for Gradescope -/

structure FailureResult where
  output : String
  score : Float := 0.0
  output_format : String := "text"
  deriving ToJson

structure ExerciseResult where
  name : Name
  score : Float
  status : String
  output : String
  deriving ToJson

structure GradingResults where
  tests : Array ExerciseResult
  output: String
  output_format: String := "text"
  deriving ToJson

/-! ### Error reporting -/

def getErrorsStr (ml : MessageLog) : IO String := do
  let errorMsgs := ml.toList.filter (fun m => m.severity == .error)
  let errors ← errorMsgs.mapM (λ m => m.toString)
  let errorTxt := errors.foldl (λ acc e => acc ++ "\n" ++ e) ""
  return errorTxt

-- Throw error and show it to the student, optionally providing additional
-- information for the instructor only
def exitWithError {α} (isLocal? : Bool) (errMsg : String) (instructorInfo := "") : IO α := do
  let result : FailureResult := {output := errMsg}
  if !isLocal? then
    IO.FS.writeFile resultsJsonPath (toJson result).pretty
  throw <| IO.userError (errMsg ++ "\n" ++ instructorInfo)

/-! ### Grading. -/

def defaultValidAxioms : Array Name :=
  #["Classical.choice".toName,
    "Quot.sound".toName,
    "propext".toName,
    "funext".toName]

def axiomHasCorrectType (ax : Name) (sheet submission : Environment) : Bool :=
  match (sheet.find? ax, submission.find? ax) with
    | (some sheetConst, some subConst) => sheetConst.type == subConst.type
    | _                                => false

def findInvalidAxiom (submissionAxioms : List Name)
                     (sheet submission : Environment)
                     (validAxioms : Array Name) : Option Name := do
  for ax in submissionAxioms do
    let isBaseAxiom := validAxioms.contains ax
    let isTaggedAxiom := legalAxiomAttr.hasTag sheet ax
    let isTypeCorrect := axiomHasCorrectType ax sheet submission

    -- If the axiom is not one of our predefined acceptable axioms, and is
    -- also not tagged in the stencil as legal, then it's invalid
    if ! (isBaseAxiom || isTaggedAxiom) || ! isTypeCorrect then
      return ax
  none

def gradeSubmission (solutionEnv submissionEnv : Environment) : IO (Array ExerciseResult) := do
  let mut gradingInfo := #[]
  for (name, constInfo) in solutionEnv.constants do
    if let some pts := autogradedProofAttr.getParam? solutionEnv name then
      gradingInfo := gradingInfo.push (constInfo, pts)

  let ctx : Core.Context := { fileName := "", fileMap := default }
  let cstate : Core.State := { env := solutionEnv }

  let mut exerciseResults : Array ExerciseResult := #[]
  for (exercise, pts) in gradingInfo do
    println! s!"grading {exercise.name}"
    -- check if answer is present
    if let none := submissionEnv.find? exercise.name then
      exerciseResults := exerciseResults.push {
        name   := exercise.name,
        score  := 0.0,
        status := "failed",
        output := s!"Missing answer for {exercise.name}.\n"
      }
      continue

    -- answer is present
    let answer := (submissionEnv.find? exercise.name).get!

    -- check if answer has the same type as exercise
    let (isEq, _, _) <- (Meta.isDefEq exercise.type answer.type).toIO ctx cstate
    if !isEq then
      exerciseResults := exerciseResults.push {
        name   := exercise.name,
        score  := 0.0,
        status := "failed",
        output := "Type is different from expected:\n"
                ++ s!"  Exercise: {exercise.type}\n"
                ++ s!"  Submission: {answer.type}"
      }
      continue

    -- check if answer is unsafe or partial
    if answer.isUnsafe || answer.isPartial then
      exerciseResults := exerciseResults.push {
        name   := exercise.name,
        score  := 0.0,
        status := "failed",
        output := s!"Answer for {exercise.name} is unsafe or partial."
      }
      continue

    -- check if answer has a value
    if !answer.hasValue then
      exerciseResults := exerciseResults.push {
        name   := exercise.name,
        score  := 0.0,
        status := "failed",
        output := s!"Answer for {exercise.name} does not have a value."
      }
      continue

    -- check if answer value uses sorry
    if answer.value!.hasSorry then
      exerciseResults := exerciseResults.push {
        name   := exercise.name,
        score  := 0.0,
        status := "failed",
        output := s!"Answer for {exercise.name} uses sorry."
      }
      continue

    -- check if answer only uses valid axioms
    let validAxioms :=
      if let some ax := validAxiomsAttr.getParam? solutionEnv exercise.name then ax
      else defaultValidAxioms

    let (_, submissionState) :=
      ((CollectAxioms.collect exercise.name).run submissionEnv).run {}

    if let some badAx :=
      findInvalidAxiom submissionState.axioms.toList solutionEnv submissionEnv validAxioms
    then
      exerciseResults := exerciseResults.push {
        name   := exercise.name,
        score  := 0.0,
        status := "failed",
        output := s!"Answer for {exercise.name} uses an invalid axiom: {badAx}."
      }
      continue

    -- answer is correct
    exerciseResults := exerciseResults.push {
      name := exercise.name,
      score := pts,
      status := "passed",
      output := "Passed all tests"
    }

  return exerciseResults

/-! ### Main -/

structure Config where
  solution   : Option String
  submission : Option String
  isLocal?  : Bool

def parseArgs (args : List String) : IO Config := do
  match args with
  | "--solution" :: solution :: args =>
    let cfg <- parseArgs args
    return { cfg with solution }
  | "--submission" :: submission :: args =>
    let cfg <- parseArgs args
    return { cfg with submission }
  | "--local" :: args =>
    let cfg <- parseArgs args
    return { cfg with isLocal? := true }
  | [] => return {
      solution := none,
      submission := none,
      isLocal? := false
    }
  | _ => throw <| IO.userError "Error parsing arguments."

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)

  let cfg <- parseArgs args

  let solutionName := cfg.solution.get!
  let solutionPath : FilePath := solutionName

  let submissionName := cfg.submission.get!
  let submissionPath : FilePath := submissionName

  let mut output := ""

  -- read the solution and submission files

  let solutionContents <- IO.FS.readFile solutionPath
  let solutionCtx := Parser.mkInputContext solutionContents solutionName

  let submissionContents <- IO.FS.readFile submissionPath
  let submissionCtx := Parser.mkInputContext submissionContents submissionName

  -- parse the grading metadata

  let (solutionHeader, parserState, messages) <- Parser.parseHeader solutionCtx
  let (solutionHeaderEnv, messages) <- processHeader solutionHeader {} messages solutionCtx

  if messages.hasErrors then
    exitWithError cfg.isLocal? (instructorInfo := (← getErrorsStr messages)) <|
      "There was an error processing the assignment template's imports. This "
      ++ "error is unexpected. Please notify your instructor and provide a "
      ++ "link to your submission."

  let solutionCmdState := Command.mkState solutionHeaderEnv messages {}
  let solutionFrontEndState <- IO.processCommands solutionCtx parserState solutionCmdState

  let messages := solutionFrontEndState.commandState.messages
  let solutionEnv := solutionFrontEndState.commandState.env

  if messages.hasErrors then
    exitWithError cfg.isLocal? (instructorInfo := (← getErrorsStr messages)) <|
      "There was an error processing the assignment template. This "
      ++ "error is unexpected. Please notify your instructor and provide a "
      ++ "link to your submission."

  -- parse the submission.

  let (submissionHeader, parserState, messages) <- Parser.parseHeader submissionCtx
  let (submissionHeaderEnv, messages) <- processHeader submissionHeader {} messages submissionCtx

  let err ← getErrorsStr messages
  output := output ++
    if messages.hasErrors then
      "Warning: Your submission contains one or more errors, which are "
      ++ "listed below. You should attempt to correct these errors prior "
      ++ "to your final submission. Any responses with errors will be "
      ++ "treated by the autograder as containing \"sorry.\"\n"
      ++ err
    else ""

  let submissionCmdState := Command.mkState submissionHeaderEnv messages {}
  let submissionFrontEndState <- IO.processCommands submissionCtx parserState submissionCmdState

  let messages := submissionFrontEndState.commandState.messages
  let submissionEnv := submissionFrontEndState.commandState.env

  -- grade the submission

  let tests <- gradeSubmission solutionEnv submissionEnv
  let results : GradingResults := { tests, output }

  -- output results

  if !cfg.isLocal? then
    IO.FS.writeFile resultsJsonPath (toJson results).pretty

  println! (toJson results).pretty
