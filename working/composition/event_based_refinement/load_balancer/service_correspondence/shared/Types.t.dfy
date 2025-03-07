module Types {
    type ClientId = nat
    type SeqNo = nat

    datatype Option<T> = Some(value:T) | None

    newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100

    datatype Message<MessageType> = Message(src: ClientId, dest: ClientId, msg: MessageType)

    datatype MessageOps = MessageOps(recv: set<Message<seq<byte>>>, send: set<Message<seq<byte>>>)
}