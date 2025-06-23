interface Signer {
    function digestNonce(uint nonce) external returns (uint);
}

contract Test {
    struct Payload {
        uint[] items;
        uint[] moreItems;
        uint itemNonce;
        address signer;
    }

    mapping (uint => Payload) pendingPayloads;

    function getSigner(uint id) external returns (uint) {
        Payload memory p = pendingPayloads[id];
        return Signer(p.signer).digestNonce(p.itemNonce);
    }
}