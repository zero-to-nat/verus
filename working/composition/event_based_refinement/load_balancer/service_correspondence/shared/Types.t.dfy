module Types {
    type ClientId = nat
    type SeqNo = nat

    datatype Option<T> = Some(value:T) | None

    newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100

    datatype MessageOps = MessageOps(recv: set<seq<byte>>, send: set<seq<byte>>)
}