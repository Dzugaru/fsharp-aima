open System.Net
open System.Net.Sockets


let server = new TcpListener(IPAddress.Any, 3137)
server.Start()
printfn "Listening.."
let socket = server.AcceptSocket()
printfn "Client connected"
let buffer : byte[] = Array.zeroCreate 16
let n = socket.Receive(buffer)
printfn "%A" (Array.take n)