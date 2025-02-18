include "ServerSpec.t.dfy"
include "../shared/Network.t.dfy"

module ServerNetwork refines AbstractNetwork {
    datatype Message = ServerRequest(request: ServiceRequest<(int, int)>) | ServerResponse(response: ServiceResponse<int>)
}