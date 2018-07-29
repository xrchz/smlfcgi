(*
  A FastCGI v1 wrapper to wrap around an ordinary CGI/1.1 program.
  The resulting FastCGI application is a non-multiplexing Responder.

  For simplicity, assumes the CGI app reads all of standard input before
  producing output.

  Usage:
    smlfcgi app.cgi [port=5000]
*)

(* misc lib *)

fun Word8_fromChar c = Word8.fromInt (Char.ord c)
fun Word8Vector_fromCharVector vec =
  Word8Vector.tabulate(CharVector.length vec,
    (fn i => Word8_fromChar (CharVector.sub(vec, i))))

fun Char_fromWord8 b = Char.chr (Word8.toInt b)
fun CharVector_fromWord8Vector vec =
  CharVector.tabulate(Word8Vector.length vec,
    (fn i => Char_fromWord8 (Word8Vector.sub(vec, i))))

fun failwith msg = raise (Fail msg)
fun assert b msg = if b then () else failwith msg

val format_env =
  List.map
    (fn (k,v) => String.concat[CharVector_fromWord8Vector k, "=",
                               CharVector_fromWord8Vector v])

fun debug s = TextIO.print(s^"\n")

(* end misc lib *)

(* FCGI constants *)

val FCGI_LISTENSOCK_FILENO = Word8.fromInt 0
val FCGI_HEADER_LEN = 8
val FCGI_VERSION_1         = Word8.fromInt  1

val FCGI_BEGIN_REQUEST     = Word8.fromInt  1
val FCGI_ABORT_REQUEST     = Word8.fromInt  2
val FCGI_END_REQUEST       = Word8.fromInt  3
val FCGI_PARAMS            = Word8.fromInt  4
val FCGI_STDIN             = Word8.fromInt  5
val FCGI_STDOUT            = Word8.fromInt  6
val FCGI_STDERR            = Word8.fromInt  7
val FCGI_DATA              = Word8.fromInt  8
val FCGI_GET_VALUES        = Word8.fromInt  9
val FCGI_GET_VALUES_RESULT = Word8.fromInt 10
val FCGI_UNKNOWN_TYPE      = Word8.fromInt 11
val FCGI_MAXTYPE           = FCGI_UNKNOWN_TYPE
val FCGI_NULL_REQUEST_ID   = Word8.fromInt  0
val FCGI_KEEP_CONN         = Word8.fromInt  1
val FCGI_RESPONDER         = 1
val FCGI_AUTHORIZER        = 2
val FCGI_FILTER            = 3
val FCGI_REQUEST_COMPLETE  = Word8.fromInt  0
val FCGI_CANT_MPX_CONN     = Word8.fromInt  1
val FCGI_OVERLOAD          = Word8.fromInt  2
val FCGI_UNKNOWN_ROLE      = Word8.fromInt  3

val FCGI_MAX_CONNS  = Word8Vector_fromCharVector "FCGI_MAX_CONNS"
val FCGI_MAX_REQS   = Word8Vector_fromCharVector "FCGI_MAX_REQS"
val FCGI_MPXS_CONNS = Word8Vector_fromCharVector "FCGI_MPXS_CONNS"

(* end FCGI constants *)

(* socket comms *)


fun make_listener port =
  let
    val socket = INetSock.TCP.socket ()
    val sock_addr = INetSock.any port
    val () = Socket.bind (socket, sock_addr)
    val () = Socket.listen (socket, 128)
  in
    socket
  end

exception Closed

fun recvVecN (socket, n) =
  let
    val arr = Word8Array.array(n, 0wx0)
    fun loop (slice, received) =
      let
        val more = Socket.recvArr(socket, slice)
        val () = debug(String.concat["recvVecN: got ", Int.toString more, " bytes"])
        val received = received + more
      in
        if more = 0 then raise Closed
        else if n <= received then Word8Array.vector arr
        else loop (Word8ArraySlice.subslice(slice, received, NONE), received)
      end
  in
    if n = 0 then Word8Array.vector arr
    else loop (Word8ArraySlice.full arr, 0)
  end

fun sendVecs (socket, vecs) =
  let
    fun loop slice =
      if Word8VectorSlice.isEmpty slice then ()
      else let
        val sent = Socket.sendVec(socket, slice)
        val slice = Word8VectorSlice.subslice(slice, sent, NONE)
      in loop slice end
  in List.app (loop o Word8VectorSlice.full) vecs end

(* end socket comms *)

(* FCGI comms *)

fun TwoWord8s_toInt (b1,b0) =
  Word32.toInt(Word32.<<(Word32.fromInt(Word8.toInt b1), 0w8)) +
  Word8.toInt b0

fun TwoWord8s_fromInt n =
  (Word8.fromInt(Word32.toInt(Word32.>>(Word32.fromInt n, 0w8))),
   Word8.fromInt n)

fun FourWord8s_toInt (b3,b2,b1,b0) =
  Word32.toInt(Word32.<<(Word32.fromInt(Word8.toInt b3), 0w24)) +
  Word32.toInt(Word32.<<(Word32.fromInt(Word8.toInt b2), 0w16)) +
  Word32.toInt(Word32.<<(Word32.fromInt(Word8.toInt b1), 0w8)) +
  Word8.toInt b0

fun FourWord8s_fromInt n =
  (Word8.fromInt(Word32.toInt(Word32.>>(Word32.fromInt n, 0w24))),
   Word8.fromInt(Word32.toInt(Word32.>>(Word32.fromInt n, 0w16))),
   Word8.fromInt(Word32.toInt(Word32.>>(Word32.fromInt n, 0w8))),
   Word8.fromInt n)

fun makeLength n =
  if n <= 127 then
    Word8Vector.fromList[Word8.fromInt n]
  else
    let
      val n32 = Word32.fromInt n
    in
      Word8Vector.fromList[
        Word8.orb(Word8.fromInt(Word32.toInt(Word32.>>(n32, 0w24))), 0wx80),
        Word8.fromInt(Word32.toInt(Word32.>>(n32, 0w16))),
        Word8.fromInt(Word32.toInt(Word32.>>(n32, 0w8))),
        Word8.fromInt n]
    end

fun readLength slice =
  let
    val w = Word8VectorSlice.sub(slice, 0)
    val w8tow32 = Word32.fromInt o Word8.toInt
  in
    if Word8.>>(w, 0w7) = 0w0 then
      (Word8.toInt w, Word8VectorSlice.subslice(slice, 1, NONE))
    else
    let
      val w = Word32.<<(w8tow32(Word8.andb(w, 0wx7f)), 0w24)
      val x = Word32.<<(w8tow32(Word8VectorSlice.sub(slice, 1)), 0w16)
      val y = Word32.<<(w8tow32(Word8VectorSlice.sub(slice, 2)), 0w8)
      val z = Word8VectorSlice.sub(slice, 3)
    in
      (Word32.toInt w + Word32.toInt x + Word32.toInt y + Word8.toInt z,
       Word8VectorSlice.subslice(slice, 4, NONE))
    end
  end

fun make_NameValuePair ((name,value),acc) =
  let
    val nameLength = Word8Vector.length name
    val valueLength = Word8Vector.length value
  in
    value::
    name::
    makeLength valueLength::
    makeLength nameLength::
    acc
  end

fun read_NameValuePair slice =
  let
    val (nameLength, slice) = readLength slice
    val (valueLength, slice) = readLength slice
    val name = Word8VectorSlice.subslice(slice, 0, SOME nameLength)
    val value = Word8VectorSlice.subslice(slice, nameLength, SOME valueLength)
    val slice = Word8VectorSlice.subslice(slice, nameLength+valueLength, NONE)
  in
    ((Word8VectorSlice.vector name,
      Word8VectorSlice.vector value), slice)
  end

fun read_NameValuePairs vec =
  let
    fun loop slice acc =
      if Word8VectorSlice.isEmpty slice then List.rev acc
      else let val (nv,slice) = read_NameValuePair slice
      in loop slice (nv::acc) end
  in
    loop (Word8VectorSlice.full vec) []
  end

fun make_record requestType requestId content =
  let
    val (requestIdB1, requestIdB0) = requestId
    val contentLength = List.foldl (fn (v,a) => a + Word8Vector.length v) 0 content
    val (contentLengthB1, contentLengthB0) = TwoWord8s_fromInt contentLength
    val paddingLength = if 0 < contentLength then 8 - Int.mod(contentLength, 8) else 0
    val padding = Word8Vector.tabulate(paddingLength, (fn _ => 0w0))
    val header =
      Word8Vector.fromList [
        FCGI_VERSION_1,
        requestType,
        requestIdB1,
        requestIdB0,
        contentLengthB1,
        contentLengthB0,
        Word8.fromInt paddingLength]
  in
    header :: List.rev (padding::content)
  end

fun read_record socket =
  let
    val header = recvVecN (socket, FCGI_HEADER_LEN)
    val () = debug("read_record: finished reading header")
    val () = assert (Word8Vector.sub(header, 0) = FCGI_VERSION_1)
                    "Wrong FastCGI version"
    val requestType = Word8Vector.sub(header, 1)
    val requestId =  (Word8Vector.sub(header, 2),
                      Word8Vector.sub(header, 3))
    val contentLength =
      TwoWord8s_toInt(Word8Vector.sub(header, 4),
                      Word8Vector.sub(header, 5))
    val paddingLength = Word8.toInt(Word8Vector.sub(header, 6))
    val content = recvVecN(socket, contentLength)
    val _ = recvVecN(socket, paddingLength)
  in
    (requestType, requestId, contentLength, content)
  end

(* end FCGI comms *)

(* smlfcgi values *)

fun getValue (name, (_:Word8Vector.vector)) =
  if name = FCGI_MAX_CONNS then
    SOME (name, Word8Vector_fromCharVector "1")
  else if name = FCGI_MAX_REQS then
    SOME (name, Word8Vector_fromCharVector "1")
  else if name = FCGI_MPXS_CONNS then
    SOME (name, Word8Vector_fromCharVector "0")
  else NONE

(* end smlfcgi values *)

(* wrapped responder protocol *)

type proc_and_streams = {
  proc : (TextIO.instream, TextIO.outstream) Unix.proc,
  ins  : TextIO.instream,
  outs : TextIO.outstream }

fun make_proc_and_streams proc =
  let val (ins, outs) = (Unix.textInstreamOf proc, Unix.textOutstreamOf proc)
  in { proc = proc, ins = ins, outs = outs } end

datatype cgi_state =
    Waiting of Word8Vector.vector list
  | Running of proc_and_streams * bool (* receiving input *)

type request = {
  R_id : Word8.word * Word8.word,
  R_keep_conn : bool,
  R_cgi : cgi_state }

fun endRequest requestId appStatus protocolStatus =
  make_record FCGI_END_REQUEST requestId
    let val (b3,b2,b1,b0) = FourWord8s_fromInt appStatus in
      [Word8Vector.fromList
         [b3, b2, b1, b0, protocolStatus, 0w0, 0w0, 0w0]]
    end

fun endRequestFail requestId = endRequest requestId 1

fun request_type_to_string x =
  if x = FCGI_GET_VALUES then "FCGI_GET_VALUES" else
  if x = FCGI_BEGIN_REQUEST then "FCGI_BEGIN_REQUEST" else
  if x = FCGI_PARAMS then "FCGI_PARAMS" else
  if x = FCGI_STDIN then "FCGI_STDIN" else
  if x = FCGI_ABORT_REQUEST then "FCGI_ABORT_REQUEST" else
  ("unknown request: "^(Word8.toString x))

fun protocol cgi_path socket =
  let
    fun loop current_request =
      let
        fun query_server () =
          let
            val () = debug "query_server"
            val (requestType, requestId, contentLength, content) = read_record socket
            val () = debug "finished reading record"
            fun single_request handle_req =
              (case current_request of NONE =>
                 (sendVecs(socket, endRequestFail requestId FCGI_CANT_MPX_CONN);
                  loop current_request)
               | SOME req =>
                   if #R_id req <> requestId then
                     (sendVecs(socket, endRequestFail requestId FCGI_CANT_MPX_CONN);
                      loop current_request)
                   else handle_req req)
            val () = debug (request_type_to_string requestType)
          in
            if requestType = FCGI_GET_VALUES
            then
              let
                val ls = read_NameValuePairs content
                val ls = List.mapPartial getValue ls
                val vecs = List.foldl make_NameValuePair [] ls
              in
                (sendVecs(socket, make_record FCGI_GET_VALUES_RESULT requestId vecs);
                 loop current_request)
              end
            else if requestType = FCGI_BEGIN_REQUEST then
              if Option.isSome current_request then
                (sendVecs(socket, endRequestFail requestId FCGI_CANT_MPX_CONN);
                 loop current_request)
              else
                let
                  val role = TwoWord8s_toInt(Word8Vector.sub(content, 0),
                                             Word8Vector.sub(content, 1))
                in
                  if role <> FCGI_RESPONDER then
                    (sendVecs(socket, endRequestFail requestId FCGI_UNKNOWN_ROLE);
                     loop current_request)
                  else
                    let
                      val flags = Word8Vector.sub(content, 2)
                      val keep_conn = Word8.andb(flags, FCGI_KEEP_CONN) <> 0w0
                    in
                      loop (SOME {R_id = requestId,
                                  R_keep_conn = keep_conn,
                                  R_cgi = Waiting []})
                    end
                end
            else if requestType = FCGI_PARAMS then
              single_request (fn {R_id, R_keep_conn, R_cgi=Waiting params} =>
                                if contentLength = 0 then
                                  loop (SOME {R_id = R_id,
                                              R_keep_conn = R_keep_conn,
                                              R_cgi =
                                                let val proc =
                                                  Unix.executeInEnv(cgi_path, [],
                                                    format_env
                                                      (read_NameValuePairs
                                                        (Word8Vector.concat (List.rev params))))
                                                in Running (make_proc_and_streams proc, true) end})
                                else
                                  loop (SOME {R_id  = R_id,
                                              R_keep_conn = R_keep_conn,
                                              R_cgi = Waiting (content :: params)})
                              | _ => failwith "FCGI_PARAMS: cgi already running")
            else if requestType = FCGI_STDIN then
              single_request (fn {R_cgi=Running (ps as {outs, ...}, true), R_id, R_keep_conn} =>
                                if 0 < contentLength then
                                  (debug "FCGI_STDIN: sending content";
                                   TextIO.output(outs, CharVector_fromWord8Vector content);
                                   loop current_request)
                                else (debug "FCGI_STDIN: end of content";
                                      TextIO.closeOut outs;
                                      loop (SOME {R_cgi = Running (ps, false),
                                                  R_id = R_id, R_keep_conn = R_keep_conn}))
                              | _ => failwith "FCGI_STDIN: cgi not running or not accepting stdin")
            else if requestType = FCGI_ABORT_REQUEST then
              single_request (fn {R_cgi, R_keep_conn, ...} =>
                let
                  val st =
                    case R_cgi of Waiting _ => 0
                    | Running ({proc,...},_) =>
                        (Unix.kill(proc, Posix.Signal.term);
                         case Unix.fromStatus (Unix.reap proc) of
                                     Unix.W_EXITED => 0
                                   | Unix.W_EXITSTATUS w => Word8.toInt w
                                   | _ => 255)
                in
                  (sendVecs(socket, endRequest requestId st FCGI_REQUEST_COMPLETE);
                   if R_keep_conn then loop NONE else () (*Socket.close socket*))
                end)
            else
              (sendVecs(socket,
                        make_record FCGI_UNKNOWN_TYPE requestId
                          [Word8Vector.fromList[requestType,0w0,0w0,0w0,0w0,0w0,0w0,0w0]]);
               loop current_request)
          end
          handle Closed => (debug"Server closed connection";
                            debug(Date.toString(Date.fromTimeUniv(Time.now())));
                            OS.Process.sleep(Time.fromMilliseconds 800);
                            () (*Socket.close socket*))
        val () = debug "protocol loop"
        val () = debug(Date.toString(Date.fromTimeUniv(Time.now())))
        val () = OS.Process.sleep(Time.fromMilliseconds 800)
      in
        case current_request of
          SOME {R_cgi = Running (       _        , true), ...} => query_server ()
        | SOME {R_cgi = Running ({proc, ins, ...},  _  ), R_keep_conn, R_id} =>
            let
              val output = TextIO.inputN(ins, 256)
              val n = String.size output
              val () = sendVecs (socket, make_record FCGI_STDOUT R_id
                                         [Word8Vector_fromCharVector output])
            in
              if n < 256 then
                (assert (OS.Process.isSuccess(Unix.reap proc)) "cgi died";
                 (*
                 sendVecs (socket, make_record FCGI_STDERR R_id [Word8Vector.fromList []]);
                 *)
                 debug("before end request");
                 sendVecs (socket, endRequest R_id 0 FCGI_REQUEST_COMPLETE);
                 debug("after end request");
                 debug(Date.toString(Date.fromTimeUniv(Time.now())));
                 OS.Process.sleep(Time.fromMilliseconds 800);
                 debug("succesfully ended request, keep_conn = "^(Bool.toString R_keep_conn));
                 if R_keep_conn then loop NONE else () (*Socket.close socket*))
              else
                 loop current_request
            end
        | _ => query_server ()
      end
  in loop NONE end

(* end wrapped responder protocol *)

fun main () =
  let
    val args = CommandLine.arguments ()
    val cgi_path = List.hd args handle Empty =>
                     failwith(String.concat["Usage: ",CommandLine.name()," app.cgi"])
    val port = Option.valOf (Int.fromString (List.hd (List.tl args)))
                  handle Empty => 5000
                       | Option => failwith("Could not understand port argument")
    (*
    fun loop () =
      let
        val listener = make_listener port
        val (socket, _) = Socket.accept listener
        val () = Socket.close listener
        val () = protocol cgi_path socket
        val () = Socket.close socket
      in
        loop ()
      end
      *)
    val listener = make_listener port
    fun loop () =
         let
          val () =
          (debug("before accept");
           debug(Date.toString(Date.fromTimeUniv(Time.now())));
           OS.Process.sleep(Time.fromMilliseconds 800))
          val (socket, _) = Socket.accept listener in
         (protocol cgi_path socket;
          (*
          debug("before shutdown");
          debug(Date.toString(Date.fromTimeUniv(Time.now())));
          OS.Process.sleep(Time.fromMilliseconds 800);
          Socket.shutdown(socket, Socket.NO_SENDS);
          *)
          (*
          debug("before try receive");
          debug(Date.toString(Date.fromTimeUniv(Time.now())));
          OS.Process.sleep(Time.fromMilliseconds 800);
          (case Socket.recvVecNB(socket,64) of NONE => debug("couldn't receive more")
           | SOME str => debug("received this ("^(Int.toString(Word8Vector.length str))^"): "^(CharVector_fromWord8Vector str)));
          *)
          debug("before close");
          debug(Date.toString(Date.fromTimeUniv(Time.now())));
          OS.Process.sleep(Time.fromMilliseconds 800);
          Socket.close socket;
          debug("before reloop");
          debug(Date.toString(Date.fromTimeUniv(Time.now())));
          OS.Process.sleep(Time.fromMilliseconds 800);
          loop ())
          end
    (*
    val listener = make_listener port
    fun loop () =
      let
          val () =
          (debug("before accept");
           debug(Date.toString(Date.fromTimeUniv(Time.now())));
           OS.Process.sleep(Time.fromMilliseconds 800))
      val (socket, _) = Socket.accept listener
      in (protocol cgi_path socket;
          debug("before shutdown");
          debug(Date.toString(Date.fromTimeUniv(Time.now())));
          OS.Process.sleep(Time.fromMilliseconds 800);
          Socket.shutdown(socket, Socket.NO_RECVS_OR_SENDS);
          debug("before try receive");
          debug(Date.toString(Date.fromTimeUniv(Time.now())));
          OS.Process.sleep(Time.fromMilliseconds 800);
          (case Socket.recvVecNB(socket,64) of NONE => debug("couldn't receive more")
           | SOME str => debug("received this ("^(Int.toString(Word8Vector.length str))^"): "^(CharVector_fromWord8Vector str)));
          debug("before close");
          debug(Date.toString(Date.fromTimeUniv(Time.now())));
          OS.Process.sleep(Time.fromMilliseconds 800);
          Socket.close socket;
          debug("before reloop");
          debug(Date.toString(Date.fromTimeUniv(Time.now())));
          OS.Process.sleep(Time.fromMilliseconds 800);
          loop ()) end
    *)
  in loop () end
  handle e => (TextIO.output(TextIO.stdErr,
                             String.concat["Exception: ", exnMessage e, "\n"]);
               OS.Process.exit OS.Process.failure)
