structure Main :> sig

  val check : string -> unit
  val commit : unit -> unit
  val load : string -> unit
  val reset : unit -> unit

end = struct

  structure IOU = IOUtil
  structure TIO = TextIO

  structure E = Env
  structure K = Kernel
  structure P = Parse
  structure R = Report

  val env = E.new ()

  fun check filename =
    let val src = IOU.withInputFile (filename, TIO.inputAll) TIO.stdIn
    in
      E.rollback env;
      K.validate env (P.parse src)
        handle ex => (E.rollback env; R.report filename src ex) end

  fun commit () = E.commit env

  fun load filename = check filename before commit ()

  fun reset () = E.reset env

end
