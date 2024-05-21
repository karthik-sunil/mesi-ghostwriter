-- BASELINE MSI + E STATE


----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
    ProcCount: 3;          -- number processors
    ValueCount:   1;       -- number of data values.
    ScribbleValueCount: 1;
    VC0: 0;                -- 
    VC1: 1;                --
    VC2: 2;                --
    VC3: 3;
    -- QMax: 2;
    NumVCs: 4;
    NetMax: 6;
    timeout: 0;

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
    Proc: scalarset(ProcCount);   -- unordered range of processors
    Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
    Home: enum { HomeType };      -- need enumeration for IsMember calls
    Node: union { Home , Proc };
    ProcCountType: 0..ProcCount;
    ScribbleValue: scalarset(ScribbleValueCount);
    counterType: 0..timeout;

    VCType: VC0..NumVCs-1;

    MessageType: enum {
        --VC0
        GetS, 
        GetM, 
        PutS, 
        PutM, 
        PutE,

        --VC1
        FwdGetS, 
        FwdGetM, 
        Inv, 
        PutSAck, 
        PutMAck, 
        PutEAck,

        --VC3
        GetEAck,
        GetSAck,  
        FwdGetSAck,
        GetMAck,
        FwdGetMAck,
        InvAck
    };

    Message:
        Record
            mtype: MessageType;
            src: Node;
            -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
            vc: VCType;
            val: Value;
            fwdreq: Node;
            -- isex: boolean;
        End;

    HomeState:
        Record
            state: enum {
                HS_I,
                HS_S,
                HS_M,
                HS_E,

                HT_SD,
                HT_MM,
                HT_SM,
                HT_EM
            };
            owner: Node;
            -- newOwner: Node; --Not there in twostate 74-76
            sharers: multiset [ProcCount] of Node;    --No need for sharers in this protocol, but this is a good way to represent them
            -- mshr: multiset [ProcCount] of Node;
            val: Value; 
        End;

    ProcState:
        Record
            state: enum {
                PS_I,
                PS_S,
                PS_M,
                PS_E,
                PS_GS,
                PS_GI,

                PT_ISD,
                PT_IMAD,
                PT_IMA,

                PT_SMAD,
                PT_SMA,

                PT_MIA,
                PT_SIA,
                PT_IIA,
                PT_EIA
            };
            val: Value;
            scribbleVal: ScribbleValue;
            counter: counterType;
        End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
    HomeNode:  HomeState;
    Procs: array [Proc] of ProcState;
    Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
    InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
    msg_processed: boolean;
    LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware
    AckCountSharers: multiset[ProcCount] of Node;
----------------------------------------------------------------------
-- Other Procedures
---------------------------------------------------------------------- 
-- Procedure PrintMessageType(mtype: MessageType);
-- Begin
--   switch mtype:
--     case GetS:
--         put("GetS");
--     case GetM:
--         put("GetM");    
--     case PutS:
--         put("PutM");
--     case PutE:
--         put("PutE");
--     case FwdGetS:
--         put("FwdGetS");
--     case FwdGetM:
--         put("FwdGetM");
--     case Inv:
--         put("Inv");
--     case PutSAck:
--         put("PutSAck");
--     case PutMAck:
--         put("PutMAck");
--     case PutEAck:
--         put("PutEAck");
--     case GetEAck:
--         put("GetEAck");
--     case GetSAck:
--         put("GetSAck");
--     case GetMAck:
--         put("GetMAck");
--     case FwdGetMAck:
--         put("FwdGetMAck");
--     case FwdGetSAck:
--         put("FwdGetSAck");
--     case InvAck:
--         put("InvAck");
--   endswitch;
-- End;



Procedure Send(
    mtype:MessageType;
    dst:Node;
    src:Node;
    vc:VCType;
    val:Value;
    fwdreq:Node;
);
var msg:Message;
Begin
    -- PrintMessageType(mtype);
    Assert (!IsUndefined(dst)) "Net Indexing Incorrect";
    Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
    msg.mtype := mtype;
    msg.src   := src;
    msg.vc    := vc;
    msg.val   := val;
    msg.fwdreq := fwdreq;
    MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
    error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
    error "Unhandled state!";
End;

-- These aren't needed for Valid/Invalid protocol, but this is a good way of writing these functions
Procedure AddToSharersList(n:Node);
Begin
    if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
    then
        MultiSetAdd(n, HomeNode.sharers);
    endif;
End;

Function IsSharer(n:Node) : Boolean;
Begin
    return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Function CountSharers() : ProcCountType;
Begin
    return MultiSetCount(i:HomeNode.sharers, true);
End;

Procedure RemoveFromSharersList(n:Node);
Begin
    MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

Function CountM() : ProcCountType;
var mcount: ProcCountType;
Begin
    mcount := 0;
    for n:Proc do
        if Procs[n].state = PS_M
        then 
            mcount := mcount + 1;
        endif;
    endfor;
    return mcount;
End;

Function CountE() : ProcCountType;
var ecount: ProcCountType;
Begin
    ecount := 0;
    for n:Proc do
        if Procs[n].state = PS_E
        then 
            ecount := ecount + 1;
        endif;
    endfor;
    return ecount;
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
    for n:Node do
        if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
        then
            if n != rqst
            then 
                -- Send invalidation message here 
                Send(Inv, n, HomeType, VC2, undefined, rqst);
            endif;
        endif;
    endfor;
End;

-- Copies all sharers except requestor
Procedure CopyAckCountSharers(rqst:Node);
Begin
    for n:Node do
        if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
        then
            if n != rqst
            then 
                MultiSetAdd(n, AckCountSharers);
            endif;
        endif;
    endfor;
End;

/*
Procedure CopyAckCountSharers();
Begin
    undefine AckCountSharers;
    for n:Node do
        if (IsMember(n, Proc) & MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
        then
            MultiSetAdd(n, AckCountSharers);
        endif;
    endfor;
End;
*/

Procedure RemoveFromAckCountSharers(n:Node);
Begin
    MultiSetRemovePred(i:AckCountSharers, AckCountSharers[i] = n);
End;

Function CountAckCountSharers() : ProcCountType;
Begin
    return MultiSetCount(i:AckCountSharers, true);
End;


----------------------------------------------------------------------
-- Receive Procedures
----------------------------------------------------------------------

Procedure HomeReceive(msg:Message);
var cnt:ProcCountType;  -- for counting sharers
Begin
    cnt := MultiSetCount(i:HomeNode.sharers, true); 

    -- default to 'processing' message.  set to false otherwise
    msg_processed := true;

    switch HomeNode.state
        case HS_I:
            switch msg.mtype
                case GetS:
                    --Send data to req
                    Send(GetEAck, msg.src, HomeType, VC3, HomeNode.val, undefined);
                    --set owner to req
                    HomeNode.owner := msg.src;
                    --Go to E
                    HomeNode.state := HS_E;

                case GetM:
                    -- I believe this will be needed because it is used in IMAD to IMA/M
                    HomeNode.sharers := undefined;
                    CopyAckCountSharers(msg.src);
                    --Send data to req
                    Send(GetMAck, msg.src, HomeType, VC3, HomeNode.val, undefined);
                    --Set owner to req
                    HomeNode.owner := msg.src;
                    --Go to M
                    HomeNode.state := HS_M;

                case PutS:
                    --Last/Not Last does not matter
                    --Send putack to req
                    Send(PutSAck, msg.src, HomeType, VC3, undefined, undefined);

                case PutM:

                    if (HomeNode.owner != msg.src)
                    then
                        --Non Owner
                        --Send putack to req
                        Send(PutMAck, msg.src, HomeType, VC3, undefined, undefined);
                    else
                        --Owner
                        --NOT x POSSIBLE ACC TO SORIN
                        ErrorUnhandledMsg(msg, HomeType);
                    endif;
                    

                case FwdGetSAck: -- dir can only get data from fwdgetsack
                    --NOT x POSSIBLE ACC TO SORIN
                    ErrorUnhandledMsg(msg, HomeType);

                case PutE:
                    if (msg.src = HomeNode.owner) --owner sends pute
                    then
                        --NOT POSSIBLE ACCORDING TO SORIN
                        ErrorUnhandledMsg(msg, HomeType);
                    else --non owner sends pute
                        --send putack to req
                        Send(PutEAck, msg.src, HomeType, VC1, undefined, undefined);
                    endif;

                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case HS_M:
            switch msg.mtype
                case GetS:
                    --Send fwdgets to owner
                    Send(FwdGetS, HomeNode.owner, HomeType, VC1, undefined, msg.src);
                    --Add req and owner to sharers
                    AddToSharersList(msg.src);
                    AddToSharersList(HomeNode.owner);
                    --Clear owner
                    HomeNode.owner := undefined;
                    --Go to SD
                    HomeNode.state := HT_SD;

                case GetM:
                    /*
                    --Send fwdgetm to owner
                    Send(FwdGetM, HomeNode.owner, HomeType, VC1, undefined, msg.src);
                    --Set owner to req
                    HomeNode.owner := msg.src;
                    */

                    -- go to MM
                    HomeNode.state := HT_MM;
                    -- send fwdgetm to owner
                    Send(FwdGetM, HomeNode.owner, HomeType, VC1, undefined, msg.src);

                case PutS:
                    --Last/Not Last does not matter
                    --Send putack to req
                    Send(PutSAck, msg.src, HomeType, VC1, undefined, undefined);

                case PutM:
                    
                    if (HomeNode.owner = msg.src) --Owner
                    then
                        --Copy data to memory
                        HomeNode.val := msg.val;
                        --Clear owner
                        HomeNode.owner := undefined;
                        --Send putack to req
                        Send(PutMAck, msg.src, HomeType, VC1, undefined, undefined);
                        --Go to Invalid
                        HomeNode.state := HS_I;
                    else --NonOwner
                        --Send putack to req
                        Send(PutMAck, msg.src, HomeType, VC1, undefined, undefined);
                    endif;

                case FwdGetSAck:
                    --NOT x POSSIBLE ACC TO SORIN
                    ErrorUnhandledMsg(msg, HomeType);

                case PutE:
                    if (msg.src = HomeNode.owner) --owner sends pute
                    then
                        --NOT POSSIBLE ACCORDING TO SORIN
                        ErrorUnhandledMsg(msg, HomeType);
                    else --non owner sends pute
                        --send putack to req
                        Send(PutEAck, msg.src, HomeType, VC1, undefined, undefined);
                    endif;

                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case HS_S: 
            switch msg.mtype
                case GetS:
                    --Send data to req
                    Send(GetSAck, msg.src, HomeType, VC3, HomeNode.val, undefined);
                    --Add req to sharers
                    AddToSharersList(msg.src);

                case GetM:

                    -- send getmack to requestor
                    Send(GetMAck, msg.src, HomeType, VC3, HomeNode.val, undefined);

                    if (CountSharers() = 1 & IsSharer(msg.src)) --only sharer requests it
                    then
                        HomeNode.state := HS_M;
                        HomeNode.owner := msg.src;
                        HomeNode.sharers := undefined;
                    else
                        -- go to state SM
                        HomeNode.state := HT_SM;
                        -- send inv to all current sharers
                        SendInvReqToSharers(msg.src);
                        -- copy ack count sharers
                        CopyAckCountSharers(msg.src);

                        -- remove requestor from sharer - TRY - DONE
                        RemoveFromSharersList(msg.src);
                    endif;

                    /* commenting old part - trying new
                    --Send data to req
                    Send(GetMAck, msg.src, HomeType, VC3, HomeNode.val, undefined);
                    --Send inv to sharers
                    SendInvReqToSharers(msg.src);
                    --Clear sharers
                    CopyAckCountSharers(msg.src); --making a copy as I will be clearing the sharers in the dir
                    HomeNode.sharers := undefined;
                    --Set owner to req
                    HomeNode.owner := msg.src;
                    --Go to Modified
                    HomeNode.state := HS_M;
                    */

                case PutS:

                    if (CountSharers() = 1 & IsSharer(msg.src)) --Last
                    then --is sharer added because otherwise you do not need to inv
                        --Remove req from sharers
                        RemoveFromSharersList(msg.src);
                        --Send putack to req
                        Send(PutSAck, msg.src, HomeType, VC1, undefined, undefined);
                        --Go to Invalid
                        HomeNode.state := HS_I;
                    else --Not Last
                        --Remove req from sharers
                        RemoveFromSharersList(msg.src);
                        --Send putack to req
                        Send(PutSAck, msg.src, HomeType, VC1, undefined, undefined);
                    endif;

                case PutM:
                    --Owner
                    --NOT x POSSIBLE ACC TO SORIN

                    --Non Owner
                    if (msg.src != HomeNode.owner)
                    then
                        --Remove req from sharers
                        RemoveFromSharersList(msg.src);
                        --Send putack to req
                        Send(PutMAck, msg.src, HomeType, VC1, undefined, undefined);
                    else
                        ErrorUnhandledMsg(msg, HomeType);
                    endif;

                    -- TRY
                    -- if last sharer, then go to I
                    if (CountSharers() = 0) -- it must have gotten removed above, so 0
                    then
                        HomeNode.state := HS_I;
                    else
                    endif;

                case FwdGetSAck:
                    --NOT x POSSIBLE ACC TO SORIN
                    ErrorUnhandledMsg(msg, HomeType);

                case PutE:
                    if (msg.src = HomeNode.owner) --owner sends pute
                    then
                        --NOT POSSIBLE ACCORDING TO SORIN
                        ErrorUnhandledMsg(msg, HomeType);
                    else --non owner sends pute
                        --remove req from sharers
                        RemoveFromSharersList(msg.src);
                        --send putack to req
                        Send(PutEAck, msg.src, HomeType, VC1, undefined, undefined);

                        if (CountSharers() = 0)
                        then
                            HomeNode.state := HS_I;
                        endif;
                    endif;

                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;
            
        case HT_SD:
            switch msg.mtype
                case GetS:
                    --Stall
                    msg_processed := false;

                case GetM:
                    --Stall
                    msg_processed := false;

                case PutS:
                    msg_processed := false;
                    /*
                    --Last/Not Last does not matter
                    --Remove req from sharers
                    RemoveFromSharersList(msg.src);
                    --Send putack to req
                    Send(PutSAck, msg.src, HomeType, VC1, undefined, undefined);
                    */

                case PutM:
                    msg_processed := false;
                    /*
                    --Owner
                    --NOT x POSSIBLE ACC TO SORIN

                    --Non Owner
                    if (msg.src != HomeNode.owner)
                    then
                        --Remove req from sharers
                        RemoveFromSharersList(msg.src);
                        --Send putack to req
                        Send(PutMAck, msg.src, HomeType, VC1, undefined, undefined);
                    else
                        --empty
                    endif;
                    */

                case FwdGetSAck:
                    --Copy data to memory
                    HomeNode.val := msg.val;
                    --Go to Shared
                    HomeNode.state := HS_S;

                case PutE:
                    msg_processed := false;
                    /*
                    if (msg.src = HomeNode.owner) --owner sends pute
                    then
                        --NOT POSSIBLE ACCORDING TO SORIN
                        ErrorUnhandledMsg(msg, HomeType);
                    else --non owner sends pute
                        --remove req from sharers
                        RemoveFromSharersList(msg.src);
                        --send putack to req
                        Send(PutEAck, msg.src, HomeType, VC1, undefined, undefined);
                    endif;
                    */

                else
                    ErrorUnhandledMsg(msg, HomeType);

            endswitch;

        case HT_EM:
            switch msg.mtype
                case FwdGetMAck:
                    -- go to M
                    HomeNode.state := HS_M;
                    -- change owner
                    HomeNode.owner := msg.fwdreq;

                else
                    -- ErrorUnhandledMsg(msg, HomeType);
                    msg_processed := false;
            endswitch;

        case HS_E:
            switch msg.mtype
                case GetS:
                    --forward get s to owner
                    Send(FwdGetS, HomeNode.owner, HomeType, VC1, undefined, msg.src);
                    --make owner sharer
                    AddToSharersList(HomeNode.owner);
                    --add req to sharer
                    AddToSharersList(msg.src);
                    --clear owner   
                    HomeNode.owner := undefined;
                    --go to sd
                    HomeNode.state := HT_SD;

                case GetM:
                    --fwdgetm to owner
                    Send(FwdGetM, HomeNode.owner, HomeType, VC1, undefined, msg.src);
                    --go to EM
                    HomeNode.state := HT_EM;
                    --(in EM, on receiving ack, change owner, and go to M)

                case PutS:
                    --send putack to req in both cases
                    Send(PutSAck, msg.src, HomeType, VC1, undefined, undefined);

                case PutM:
                    if (msg.src = HomeNode.owner) --from owner
                    then
                        --copy data to mem
                        HomeNode.val := msg.val;
                        --send putack to req
                        Send(PutMAck, msg.src, HomeType, VC1, undefined, undefined);
                        --clear owner
                        HomeNode.owner := undefined;
                        --go to I
                        HomeNode.state := HS_I;
                    else --from nonowner
                        --send putack to req
                        Send(PutMAck, msg.src, HomeType, VC1, undefined, undefined);
                    endif;

                case PutE:
                    if (msg.src = HomeNode.owner) --owner
                    then
                        --send putack to req
                        Send(PutEAck, msg.src, HomeType, VC1, undefined, undefined);
                        --clear owner
                        HomeNode.owner := undefined;
                        -- go to I
                        HomeNode.state := HS_I;
                    else --non owner
                        --send putack to req
                        Send(PutEAck, msg.src, HomeType, VC1, undefined, undefined);
                    endif;

                else
                    ErrorUnhandledMsg(msg, HomeType);
            endswitch;

        case HT_MM:
            switch msg.mtype
                case FwdGetMAck:
                    -- go to M
                    HomeNode.state := HS_M;
                    -- change owner
                    HomeNode.owner := msg.fwdreq;
                else
                    msg_processed := false;
                    -- stalling for other messages, no need for error unhandled
            endswitch;

        case HT_SM:
            switch msg.mtype
                case InvAck:

                    -- remove from sharer list
                    RemoveFromSharersList(msg.src);

                    if (CountSharers() = 0) -- last invack
                    then
                        -- go to M
                        HomeNode.state := HS_M;

                        -- update owner
                        HomeNode.owner := msg.fwdreq;

                    else -- not last invack
                    endif;
                else
                    msg_processed := false;
                    -- stalling for other messages, no need for error unhandled
            endswitch;

    endswitch;
End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
    msg_processed := true;

    alias ps:Procs[p].state do
    alias pv:Procs[p].val do
    
    switch ps
        case PS_GS:
            switch msg.mtype
                case Inv:
                    -- send invack to req
                    Send(InvAck, msg.fwdreq, p, VC3, pv, undefined);
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                    -- send invack to directory as well
                    Send(InvAck, HomeType, p, VC3, pv, msg.fwdreq);

                else
                    ErrorUnhandledMsg(msg, p);
            endswitch;

        case PS_GI:
            switch msg.mtype
                else
                    ErrorUnhandledMsg(msg, p);
            endswitch;

        case PS_E:
            switch msg.mtype
                case FwdGetS:
                    --send data to req and dir
                    Send(FwdGetSAck, HomeType, p, VC3, pv, msg.fwdreq);
                    Send(FwdGetSAck, msg.fwdreq, p, VC3, pv, msg.fwdreq);
                    --go to S
                    ps := PS_S;

                case FwdGetM:
                    -- send data to requestor
                    Send(FwdGetMAck, msg.fwdreq, p, VC3, pv, undefined);
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                    -- send ack to directory, dir will change state now, and also owner
                    Send(FwdGetMAck, HomeType, p, VC3, pv, msg.fwdreq);                    

                else
                    ErrorUnhandledMsg(msg, p);
            endswitch;

        case PT_EIA:
            switch msg.mtype
                case FwdGetS:
                    --send data to req and dir
                    Send(FwdGetSAck, msg.fwdreq, p, VC3, pv, undefined);
                    Send(FwdGetSAck, HomeType, p, VC3, pv, msg.fwdreq);
                    --go to SIA
                    ps := PT_SIA;

                case FwdGetM:
                    --send data to req
                    Send(FwdGetMAck, msg.fwdreq, p, VC3, pv, undefined);
                    Send(FwdGetMAck, HomeType, p, VC3, pv, msg.fwdreq);
                    --go to IIA
                    ps := PT_IIA;
                case PutEAck:
                    --go to I
                    ps := PS_I;
                    undefine pv;

                else
                    ErrorUnhandledMsg(msg, p);
            endswitch;

        case PS_I:
            switch msg.mtype
                else
                --NOTHING POSSIBLE ACCORDING TO SORIN
                ErrorUnhandledMsg(msg, p);
            endswitch;

        case PT_ISD:
            switch msg.mtype
                case GetEAck:
                    -- go to E
                    ps := PS_E;
                    pv := msg.val;

                case FwdGetS:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    -- ErrorUnhandledMsg(msg, p);
                    -- same case as below
                    msg_processed := false;

                case FwdGetM:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    -- ErrorUnhandledMsg(msg, p);
                    -- working for MSI, but in MESI
                    -- considers E state owner as owner
                    msg_processed := false;

                case Inv:
                    -- stall
                    msg_processed := false;

                case PutSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetSAck:
                    -- go to shared
                    ps := PS_S;
                    
                    -- update data value
                    pv := msg.val;

                case GetMAck:
                    -- NOT POSSIBLE ACCORDING TO ME
                    ErrorUnhandledMsg(msg, p);

                case FwdGetSAck:
                    --go to shared
                    ps := PS_S;

                    -- update data value
                    pv := msg.val;

                case FwdGetMAck:
                    -- NOT POSSIBLE ACCORDING TO ME
                    ErrorUnhandledMsg(msg, p);

                case InvAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                else
                    ErrorUnhandledMsg(msg, p);
            endswitch;

        case PT_IMAD:
            switch msg.mtype
                case FwdGetS:
                    -- stall
                    msg_processed := false;

                case FwdGetM:
                    -- stall
                    msg_processed := false;

                case Inv:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetSAck:
                    -- NOT POSSIBLE ACCORDING TO ME
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    if (CountAckCountSharers() = 0) --Ack=0
                    then
                        -- go to M
                        ps := PS_M;

                        -- update data value
                        pv := msg.val;

                    else
                        -- go to IMA
                        ps := PT_IMA;
                    endif;

                case FwdGetSAck:
                    -- NOT POSSIBLE ACCORDING TO ME
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    -- go to M
                    ps := PS_M;

                    -- update data value
                    pv := msg.val;

                case InvAck:
                    RemoveFromAckCountSharers(msg.src);

                else
                    ErrorUnhandledMsg(msg, p);

            endswitch;

        case PT_IMA:
            switch msg.mtype
                case FwdGetS:
                    -- stall
                    msg_processed := false;

                case FwdGetM:
                    -- stall
                    msg_processed := false;

                case Inv:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case InvAck:
                    if (CountAckCountSharers() = 1) --last
                    then
                        -- go to M
                        ps := PS_M;

                        -- update data value
                        pv := msg.val;

                        RemoveFromAckCountSharers(msg.src);
                    else
                        -- remove from ack count sharers
                        RemoveFromAckCountSharers(msg.src);
                    endif;

                else
                    ErrorUnhandledMsg(msg, p);

            endswitch;

        case PS_S:
            switch msg.mtype
                case FwdGetS:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetM:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case Inv:
                    -- send invack to req
                    Send(InvAck, msg.fwdreq, p, VC3, pv, undefined);
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                    -- send invack to directory as well
                    Send(InvAck, HomeType, p, VC3, pv, msg.fwdreq);

                case PutSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case InvAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                else
                    ErrorUnhandledMsg(msg, p);

            endswitch;

        case PT_SMAD:
            switch msg.mtype
                case FwdGetS:
                    -- stall
                    msg_processed := false;

                case FwdGetM:
                    -- stall
                    msg_processed := false;

                case Inv:
                    -- send invack to req
                    Send(InvAck, msg.fwdreq, p, VC3, pv, undefined);
                    -- go to IMAD
                    ps := PT_IMAD;

                    -- send invack to dir 
                    Send(InvAck, HomeType, p, VC3, pv, msg.fwdreq);

                case PutSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetSAck:
                    -- NOT POSSIBLE ACCORDING TO ME
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    if (CountAckCountSharers() = 0) --ack=0
                    then
                        -- go to M
                        ps := PS_M;
                    else
                        -- go to SMA
                        ps := PT_SMA;
                    endif;

                case FwdGetSAck:
                    -- NOT POSSIBLE ACCORDING TO ME
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    -- go to M
                    ps := PS_M;

                case InvAck:
                    -- remove from ack count sharers
                    RemoveFromAckCountSharers(msg.src);

                else
                    ErrorUnhandledMsg(msg, p);
            endswitch;

        case PT_SMA:
            switch msg.mtype
                case FwdGetS:
                    -- stall
                    msg_processed := false;

                case FwdGetM:
                    -- stall
                    msg_processed := false;

                case Inv:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case InvAck:
                    if (CountAckCountSharers() = 1) --last
                    then
                        -- go to M
                        ps := PS_M;

                        RemoveFromAckCountSharers(msg.src);
                    else
                        -- remove from ack count sharers
                        RemoveFromAckCountSharers(msg.src);
                    endif;

                else
                    ErrorUnhandledMsg(msg, p);

            endswitch;

        case PS_M:
            switch msg.mtype
                case FwdGetS:
                    -- send data to requestor and directory
                    Send(FwdGetSAck, HomeType, p, VC3, pv, undefined);
                    Send(FwdGetSAck, msg.fwdreq, p, VC3, pv, undefined);                    
                    -- go to S
                    ps := PS_S;                    

                case FwdGetM:
                    -- send data to requestor
                    Send(FwdGetMAck, msg.fwdreq, p, VC3, pv, undefined);
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                    -- send ack to directory, dir will change state now, and also owner
                    Send(FwdGetMAck, HomeType, p, VC3, pv, msg.fwdreq);

                case Inv:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetSAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case InvAck:
                    -- NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                else
                    ErrorUnhandledMsg(msg, p);

            endswitch;

        case PT_MIA:
            switch msg.mtype
                case FwdGetS:
                    -- send data to requestor and directory
                    Send(FwdGetSAck, HomeType, p, VC3, pv, undefined);
                    Send(FwdGetSAck, msg.fwdreq, p, VC3, pv, undefined);                    
                    -- go to SIA
                    ps := PT_SIA;

                case FwdGetM:
                    -- send data to requestor
                    Send(FwdGetMAck, msg.fwdreq, p, VC3, pv, undefined);
                    -- go to IIA
                    ps := PT_IIA;

                    -- send ack to directory, dir will change state now, and also owner
                    Send(FwdGetMAck, HomeType, p, VC3, pv, msg.fwdreq);

                case Inv:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutSAck:
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                case PutMAck:
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                case GetSAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetSAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case InvAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                else
                    ErrorUnhandledMsg(msg, p);

            endswitch;

        case PT_SIA:
            switch msg.mtype
                case FwdGetS:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetM:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case Inv:
                    -- send invack to req
                    Send(InvAck, msg.fwdreq, p, VC3, pv, undefined);
                    -- go to IIA
                    ps := PT_IIA;

                    -- send invack to dir as well
                    Send(InvAck, HomeType, p, VC3, pv, msg.fwdreq);

                case PutSAck:
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                case PutMAck:
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                case PutEAck:
                    ps := PS_I;
                    undefine pv;

                case GetSAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetSAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case InvAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                else
                    ErrorUnhandledMsg(msg, p);

            endswitch;

        case PT_IIA:
            switch msg.mtype
                case FwdGetS:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetM:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case Inv:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case PutSAck:
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                case PutMAck:
                    -- go to I
                    ps := PS_I;
                    undefine pv;

                case PutEAck:
                    ps := PS_I;
                    undefine pv;

                case GetSAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case GetMAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetSAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case FwdGetMAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                case InvAck:
                    --NOT POSSIBLE ACCORDING TO SORIN
                    ErrorUnhandledMsg(msg, p);

                else
                    ErrorUnhandledMsg(msg, p);

            endswitch;

    endswitch;

    endalias;
    endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)
ruleset n:Proc Do

    alias p:Procs[n] Do

        ruleset v:Value Do
            rule "Modified - Store"
                (p.state = PS_M)
            ==>
                p.val := v;      
                LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
            endrule;
        endruleset;

        -- rule "Counter Decrement"
        --     (p.state = PS_GI)
        -- ==>
        --     -- put p.counter; put "\n";
        --     if (p.counter = 0) 
        --     then
        --         p.state := PS_I;
        --     else
        --         p.counter := p.counter - 1;
        --     endif;
        -- endrule;
        -- this rule with timeout = 0 gives identical result
        -- as the "Timeout" rule

        rule "Timeout"
            (p.state = PS_GI)
        ==>
            p.state := PS_I;
        endrule;

        rule "Invalid - Load"
            (p.state = PS_I) 
        ==>
            Send(GetS, HomeType, n, VC0, undefined, undefined);
            p.state := PT_ISD;
        endrule;

        rule "Invalid - Store"
            (p.state = PS_I) 
        ==>
            Send(GetM, HomeType, n, VC0, undefined, undefined);
            p.state := PT_IMAD;
        endrule;    

        rule "Shared - Store"
            (p.state = PS_S)
        ==>
            Send(GetM, HomeType, n, VC0, undefined, undefined);
            p.state := PT_SMAD;
        endrule;

        rule "Shared - Evict"
            (p.state = PS_S)
        ==>
            Send(PutS, HomeType, n, VC0, undefined, undefined);
            p.state := PT_SIA;
        endrule;

        rule "GS - Evict"
            (p.state = PS_GS)
        ==>
            Send(PutS, HomeType, n, VC0, undefined, undefined);
            p.state := PT_SIA;
        endrule;

        rule "Modified - Evict"
            (p.state = PS_M)
        ==>
            Send(PutM, HomeType, n, VC0, p.val, undefined);
            p.state := PT_MIA;
        endrule;

        rule "Exclusive - Store"
            (p.state = PS_E)
        ==>
            p.state := PS_M;
        endrule;

        rule "Exclusive - Evict"
            (p.state = PS_E)
        ==>
            Send(PutE, HomeType, n, VC0, p.val, undefined);
            p.state := PT_EIA;
        endrule;

        ruleset sv:ScribbleValue Do
            rule "Exclusive - Scribble"
                (p.state = PS_E)
            ==>
                p.state := PS_M;
            endrule;
        endruleset;

        ruleset sv:ScribbleValue Do
            rule "Modified - Scribble"
                (p.state = PS_M)
            ==>
                p.scribbleVal := sv;
            endrule;
        endruleset;

        rule "Shared - Scribble"
            (p.state = PS_S)
        ==>
            p.state := PS_GS;
        endrule;

        rule "Invalid - Scribble"
            (p.state = PS_I)
        ==>
            p.state := PS_GI;
            p.counter := timeout;
        endrule;

    endalias;
endruleset;

-- Message delivery rules
ruleset n:Node Do    
    choose midx:Net[n] do
        alias chan:Net[n] do
        alias msg:chan[midx] do
        alias box:InBox[n] do

        -- Assert (!IsUndefined(n)) "Net Indexing Incorrect";

        -- Pick a random message in the network and deliver it
        rule "receive-net"
            (isundefined(box[msg.vc].mtype))
        ==>

            if IsMember(n, Home)
            then
                HomeReceive(msg);
            else
                ProcReceive(msg, n);
            endif;

            if ! msg_processed
            then
                -- The node refused the message, stick it in the InBox to block the VC.
                box[msg.vc] := msg;
            endif;

            MultiSetRemove(midx, chan);

        endrule;

        endalias
        endalias;
        endalias;
    endchoose;  

    -- Try to deliver a message from a blocked VC; perhaps the node can handle it now
    ruleset vc:VCType do

        rule "receive-blocked-vc"
            (! isundefined(InBox[n][NumVCs - 1 - vc].mtype))
        ==>
            if IsMember(n, Home)
            then
                HomeReceive(InBox[n][NumVCs - 1 - vc]);
            else
                ProcReceive(InBox[n][NumVCs - 1 - vc], n);
            endif;

            if msg_processed
            then
                -- Message has been handled, forget it
                undefine InBox[n][NumVCs - 1 - vc];
            endif;
            
        endrule;
    endruleset;
endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate
    for v:Value do
        HomeNode.state := HS_I;
        undefine HomeNode.owner;
        undefine HomeNode.sharers;
        HomeNode.val := v;
    endfor;

    LastWrite := HomeNode.val;

    for p:Proc do
        Procs[p].state := PS_I;
        undefine Procs[p].val;
        undefine Procs[p].scribbleVal;
        Procs[p].counter := timeout;
    endfor;

    undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

-- invariant 1
invariant "invalid implies empty owner"
    HomeNode.state = HS_I
    ->
        IsUndefined(HomeNode.owner);

-- invariant 2
invariant "value is undefined while invalid"
    Forall n : Proc Do	
        Procs[n].state = PS_I
        ->
            IsUndefined(Procs[n].val)
    end;

-- invariant 3
invariant "modified implies empty sharers list"
    HomeNode.state = HS_M
    ->
        MultiSetCount(i:HomeNode.sharers, true) = 0;

-- invariant 4
invariant "invalid implies empty sharers list"
    HomeNode.state = HS_I
    ->
        MultiSetCount(i:HomeNode.sharers, true) = 0;

-- invariant 5
invariant "values in shared state match memory"
    Forall n : Proc Do	
        HomeNode.state = HS_S & Procs[n].state = PS_S
        ->
            HomeNode.val = Procs[n].val
    end;

-- invariant 6
invariant "only one modifier"
    HomeNode.state = HS_M
    ->
        CountM() <= 1;

-- invariant 7
invariant "value in memory matches value of last write when shared"
    Forall n : Proc Do	
        HomeNode.state = HS_S
        ->
            HomeNode.val = LastWrite
    end;

-- invariant 8
invariant "value in memory matches value of last write when invalid"
    Forall n : Proc Do	
        HomeNode.state = HS_I
        ->
            HomeNode.val = LastWrite
    end;

-- invariant 9
invariant "dir in modified implies defined owner"
    HomeNode.state = HS_M
    ->
        !(IsUndefined(HomeNode.owner));

-- invariant 10
invariant "dir in modified implies no sharer procs"
    Forall n : Proc Do
        HomeNode.state = HS_M
        ->
            !(Procs[n].state = PS_S)
    end;

-- invariant 11
invariant "dir in invalid implies no sharer/modifier procs"
    Forall n : Proc Do
        HomeNode.state = HS_I
        -> 
            ((!(Procs[n].state = PS_S)) & (!(Procs[n].state = PS_M)))
    End;

-- invariant 12
invariant "dir in shared implies no owner"
    HomeNode.state = HS_S
    ->
        IsUndefined(HomeNode.owner);

-- invariant 13
invariant "proc in shared implies (either value is last write or someone else going to M)"
    Forall n : Proc Do
        Procs[n].state = PS_S
        ->
            ((Procs[n].val = LastWrite) | (HomeNode.state = HT_SM))
    end;

-- invariant 14
invariant "dir in shared implies no procs in M"
    HomeNode.state = HS_S
    ->
        Forall n : Proc Do
            !(Procs[n].state = PS_M)
        end;

-- invariant 15
invariant "proc in shared implies proc in sharers list in dir"
    Forall n: Proc Do
        Procs[n].state = PS_S
        ->
            (MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    end;

-- invariant 16
invariant "proc in M implies dir either in M or transitioning from/into M/M or E(silent write)"
    Forall n : Proc Do
        Procs[n].state = PS_M
        ->
            ((HomeNode.state = HS_M) | (HomeNode.state = HT_MM) | (HomeNode.state = HT_SD) 
            | (HomeNode.state = HT_SM) | (HomeNode.state = HT_EM) | (HomeNode.state = HS_E))
    End;

-- invariant 17
invariant "dir in shared implies non empty sharers list"
    (HomeNode.state = HS_S)
    ->
        MultiSetCount(i:HomeNode.sharers, true) > 0;    

-- invariant 17
invariant "dir in exclusive implies no sharers in dir"
    (HomeNode.state = HS_E)
    ->
        MultiSetCount(i:HomeNode.sharers, true) = 0;

-- -- invariant 18
-- invariant "dir in E implies value = last write"
--     Forall n : Proc Do	
--         HomeNode.state = HS_E
--         ->
--             HomeNode.val = LastWrite
--     end;

-- invariant 19
invariant "proc in E implies clean copy wrt dir"
    Forall n : Proc Do	
        HomeNode.state = HS_E & Procs[n].state = PS_E
        ->
            HomeNode.val = Procs[n].val
    end;

-- invariant 20
invariant "dir in E implies 1 exclusive copy"
    (HomeNode.state = HS_E)
    ->
        CountE() <= 1;

-- invariant 21
invariant "dir in E implies no procs in S"
    Forall n : Proc Do	
        HomeNode.state = HS_E
        ->
            !(Procs[n].state = PS_S)
    end;

-- invariant 22
invariant "proc in E is owner in dir OR dir is transitioning out of E"
    Forall n : Proc Do
        Procs[n].state = PS_E
        ->
            (HomeNode.owner = n & HomeNode.state = HS_E) 
            | (HomeNode.state = HT_SD) | (HomeNode.state = HT_EM) 
    end;

