module Chord

#r "nuget:Akka"
#r "nuget:Akka.FSharp"

open Akka
open Akka.FSharp
open System
open System.Security.Cryptography
open Akka.Actor
open System.Threading

let mutable nodes: list<string> = list.Empty
let INVALID_VALUE = bigint (-1)
let BIT_LENGTH = 160
let mutable firstNode = INVALID_VALUE
let mutable stop = false

// Create the Akka Actor System with default configuration
let system = create "chord" <| Configuration.defaultConfig ()

// Message types for Admin Actor
type AdminMessage =
    | InitializeSystem of nNodes: int * nRequests: int
    | TrackHops of hopsTotal: int
    | GenerateResult

// Message types for Node(peer) Actor
type NodeMessages =
    | MakeNode of idBits: int * n: bigint * isFirstNode: bool
    | JoinRing of bigint
    | FindSuccessorNode of firstPeer: bigint * id: bigint * typeOfQuery: int * fingerTableIndex: int * numberOfHops: int
    | IsSuccessorFound of bigint
    | IsKeyfound of hops: int
    | UpdateSuccessorFingerTable of successor: bigint * id: int
    | SendPredecessor
    | IsPredecessorReceived of bigint
    | FixFingerTables
    | SendNotification of bigint
    | Stabilize
    | NumberOfRequests of int
    | None

// Create the requested number of random hashed ids
let generateHashedId (numNodes: int) =
    let random = RandomNumberGenerator.Create()
    let sha1 = SHA1.Create()

    let ids =
        Array.init numNodes (fun idx ->
            let b: byte[] = Array.zeroCreate 20
            random.GetBytes(b)
            let shaHash = sha1.ComputeHash(b)
            let hashString = BitConverter.ToString(shaHash).Replace("-", "").ToLower()

            // Making sure non of the ids are negative values
            bigint.Parse("0" + hashString, System.Globalization.NumberStyles.HexNumber))

    ids

(*
    Explicitly defined function since power calculation for bigint is 
    not supported out of the box
*)
let powerOf2 (exponent: int) : bigint =
    let multiplier = bigint 2
    let mutable value = bigint 1

    for i in 1..exponent do
        value <- value * multiplier

    value

let node (mailbox: Actor<_>) =
    let mutable nextNode = 0
    let mutable idLength = 0
    let mutable currentNode = bigint (0)
    let mutable numberOfEntries = bigint (0)
    let mutable predecessorNode = INVALID_VALUE
    let mutable successorNode = INVALID_VALUE
    let mutable fingerTable: bigint[] = Array.empty

    let mutable totalHops = 0
    let mutable totalRequests = 0

    let rec listenLoop () =
        actor {
            let! receivedMessage = mailbox.Receive()
            let messageSender = mailbox.Sender()

            match receivedMessage with

            | MakeNode(idBits: int, currentNodeID: bigint, isFirstNode: bool) ->
                currentNode <- currentNodeID
                numberOfEntries <- powerOf2 idBits
                idLength <- idBits
                fingerTable <- [| for i in 1..idLength -> INVALID_VALUE |]

                (*
                    Setting predecessor and successor correctly depending on if it is 
                    the first node in the Ring or the later ones
                *)
                if isFirstNode then
                    predecessorNode <- currentNodeID
                    successorNode <- currentNodeID
                else
                    successorNode <- INVALID_VALUE
                    predecessorNode <- INVALID_VALUE

            (*
                Finding the successor node and sending appropriate messages to other or 
                requesting node
            *)
            | FindSuccessorNode(sourceNode, nodeToFind, queryType, fti, hops) ->
                let mutable isFound = false

                if currentNode >= successorNode then
                    isFound <- (nodeToFind > currentNode) || (nodeToFind <= successorNode)
                else
                    isFound <- (nodeToFind > currentNode) && (nodeToFind <= successorNode)

                if isFound then
                    let sourceNodeReference =
                        system.ActorSelection("akka://chord/user/" + string (sourceNode))

                    (*
                        Depending on the type of query made by the requesting node
                        appropriate messages are sent to the source node
                    *)
                    if queryType = 1 then
                        sourceNodeReference <! IsSuccessorFound(successorNode)
                    elif queryType = 2 then
                        sourceNodeReference <! UpdateSuccessorFingerTable(successorNode, fti)
                    elif queryType = 3 then
                        sourceNodeReference <! IsKeyfound(hops)
                else
                    let mutable isLoopRunning = true
                    let mutable i = idLength - 1
                    let mutable nextSuccessorNode = currentNode

                    while isLoopRunning do
                        let successor = fingerTable.[i]

                        if successor <> INVALID_VALUE then
                            if currentNode >= nodeToFind then
                                if (successor < nodeToFind) && (successor < nodeToFind) then
                                    nextSuccessorNode <- successor
                                    isLoopRunning <- false
                                elif (successor > nodeToFind) then
                                    nextSuccessorNode <- successor
                            elif (successor > currentNode) && (successor < nodeToFind) then
                                nextSuccessorNode <- successor
                                isLoopRunning <- false

                        i <- i - 1

                        if i = -1 then
                            isLoopRunning <- false

                    let successorNodeRef =
                        system.ActorSelection("akka://chord/user/" + string (nextSuccessorNode))

                    successorNodeRef
                    <! FindSuccessorNode(sourceNode, nodeToFind, queryType, fti, hops + 1)

            // Adding the node to the ring by finding the correct successor and updating node details
            | JoinRing(node) ->
                let nodeRef = system.ActorSelection("akka://chord/user/" + string (node))
                // Making a request from node to find it's successor
                nodeRef <! FindSuccessorNode(currentNode, currentNode, 1, 0, 0)

            // Setting the correct successor on the node details
            | IsSuccessorFound(successor) -> successorNode <- successor

            // If the successor node is not set then setting predecessor as successor wherever necessary
            | Stabilize ->
                if successorNode <> INVALID_VALUE then
                    let successorNodeRef =
                        system.ActorSelection("akka://chord/user/" + string (successorNode))

                    successorNodeRef <! SendPredecessor

            (*
                Checks if the successor node for the current node has changed if yes
                updates the predecessor for this node and sends the new successor a
                message with current node id
            *)  
            | IsPredecessorReceived(predecessor) ->
                let mutable isSuccessorChanged = false

                if currentNode >= successorNode then
                    isSuccessorChanged <- (predecessor > currentNode) || (predecessor < successorNode)
                else
                    isSuccessorChanged <- (predecessor > currentNode) && (predecessor < successorNode)

                if isSuccessorChanged then
                    successorNode <- predecessor

                let successorNodeRef =
                    system.ActorSelection("akka://chord/user/" + string (successorNode))

                successorNodeRef <! SendNotification(currentNode)

            | SendPredecessor ->
                if predecessorNode <> INVALID_VALUE then
                    messageSender.Tell(IsPredecessorReceived predecessorNode)

            (*
                Changes predecessor of the current node upon checking the valid placement
                in the chord ring
            *)
            | SendNotification(nodeID) ->
                let mutable shouldChangePredecessor = false

                if predecessorNode = currentNode then
                    shouldChangePredecessor <- true
                elif predecessorNode = INVALID_VALUE then
                    shouldChangePredecessor <- true
                else if predecessorNode >= currentNode then
                    shouldChangePredecessor <- (nodeID > predecessorNode) || (nodeID < currentNode)
                else
                    shouldChangePredecessor <- (nodeID > predecessorNode) && (nodeID < currentNode)

                if shouldChangePredecessor then
                    predecessorNode <- nodeID

            (*
                Fixes finger table for current node by finding correct details 
            *)
            | FixFingerTables ->
                if successorNode <> INVALID_VALUE then
                    nextNode <- nextNode + 1

                    if nextNode > idLength then
                        nextNode <- 1

                    let mutable v = powerOf2 (nextNode - 1)
                    v <- (currentNode + v) % numberOfEntries

                    let nodePath = "akka://chord/user/" + string (currentNode)
                    let currentNodeRef = system.ActorSelection(nodePath)

                    // Sending a message to current node to find it's successor
                    currentNodeRef <! FindSuccessorNode(currentNode, v, 2, nextNode, 0)

            | UpdateSuccessorFingerTable(successor, fid) -> fingerTable.[fid - 1] <- successor

            | IsKeyfound(hops) ->
                totalHops <- totalHops + hops
                totalRequests <- totalRequests - 1

                if totalRequests = 0 then
                    let adminRef = system.ActorSelection("akka://chord/user/admin")
                    adminRef <! TrackHops(totalHops)

            | NumberOfRequests(nReqs) -> totalRequests <- nReqs

            | None -> printfn "Not supported"

            return! listenLoop ()
        }

    listenLoop ()

let adminActor (mailbox: Actor<_>) =
    let mutable hopCount = 0
    let mutable completed = 0
    let mutable numNodes = 0
    let mutable numRequests = 0

    let rec adminLoop () =
        actor {
            let! msg = mailbox.Receive()

            match msg with
            | InitializeSystem(nNodes, nRequests) ->
                numNodes <- nNodes
                numRequests <- nRequests

            | TrackHops(hopsTotal) ->
                hopCount <- hopCount + hopsTotal
                completed <- completed + 1

                // When all nodes have sent in their hop counts, send message to self to Generate Result
                if completed.Equals(numNodes) then
                    mailbox.Self <! GenerateResult

            // Calculates average hop count and prints final output
            | GenerateResult ->
                let totalRequests = double (numRequests) * double (numNodes)
                let result = double (hopCount) / totalRequests
                printfn "The average hop count is %f" result
                stop <- true

            return! adminLoop ()
        }

    adminLoop ()

let Start (nNodes: int, nRequests: int) =

    // Spawn the admin actor and send a message to Initialize the System
    let AdminActorRef = spawn system "admin" <| adminActor
    AdminActorRef <! InitializeSystem(nNodes, nRequests)

    // Generate the hashed node IDs for each node
    let mutable nodesToAdd = []

    let stabilizeCts = new CancellationTokenSource()

    let stabilization =
        async {
            while true do
                for node in nodes do
                    let nodeActorRef = system.ActorSelection("akka://chord/user/" + node)
                    nodeActorRef.Tell Stabilize
                    nodeActorRef.Tell FixFingerTables

                do! Async.Sleep 50
        }

    Async.Start(stabilization, stabilizeCts.Token)

    let addNode (nodeID: bigint, isFirst: bool) =
        let n = spawn system (string (nodeID)) <| node
        nodes <- List.append nodes [ string (nodeID) ]

        if isFirst then
            firstNode <- nodeID
            n <! MakeNode(BIT_LENGTH, nodeID, true)
        else
            n <! MakeNode(BIT_LENGTH, nodeID, false)
            n <! JoinRing(firstNode)

        n <! NumberOfRequests(nRequests)


    let currentIds = generateHashedId (nNodes)
    let myIds: bigint list = Array.toList currentIds
    nodesToAdd <- myIds

    // Add the first node to Chord Ring
    addNode (nodesToAdd.[0], true)

    // Add remaining nodes
    for i in 1 .. nodesToAdd.Length - 1 do
        addNode (nodesToAdd.[i], false)

    // Wait for stabilization of the ring
    Threading.Thread.Sleep(20000)

    // Simulate requests
    let mutable requests = []

    let ids = generateHashedId (nRequests)
    let myIds: bigint list = Array.toList ids
    requests <- myIds

    for i in 0 .. nodesToAdd.Length - 1 do
        let nodeActorRef =
            system.ActorSelection("akka://chord/user/" + string (nodesToAdd.[i]))

        for j in 0 .. requests.Length - 1 do
            nodeActorRef <! FindSuccessorNode(nodesToAdd.[i], requests.[j], 3, 0, 0)

    let mutable keepRunning = true

    while not stop do
        keepRunning <- true

    stabilizeCts.Cancel()