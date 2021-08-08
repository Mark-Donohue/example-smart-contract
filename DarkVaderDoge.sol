// SPDX-License-Identifier: MIT
pragma solidity ^0.8.2;

// ----------------------------------------------------------------------------
// IBEP Token Standard #20 Interface
// ----------------------------------------------------------------------------
interface IBEP20 {
    function totalSupply() external view returns (uint256);
    function decimals() external view returns (uint8);
    function symbol() external view returns (string memory);
    function name() external view returns (string memory);
    function getOwner() external view returns (address);
    function balanceOf(address account) external view returns (uint256);
    function transfer(address recipient, uint256 amount) external returns (bool);
    function allowance(address _owner, address spender) external view returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);
    
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// ----------------------------------------------------------------------------
// Current Execution Context
// ----------------------------------------------------------------------------
abstract contract Context {
    constructor () { }
    
    function _msgSender() internal view returns (address) {
        return msg.sender;
    }
    
    function _msgData() internal view returns (bytes memory) {
        this;
        return msg.data;
    }
}

// ----------------------------------------------------------------------------
// Safe Math Library
// ----------------------------------------------------------------------------
library SafeMath {
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: Addition overflow");
        
        return c;
    }
    
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: Subtraction overflow");
    }
    
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;
        
        return c;
    }
    
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) {
          return 0;
        }
        
        uint256 c = a * b;
        require(c / a == b, "SafeMath: Multiplication overflow");
        
        return c;
    }
    
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: Division by zero");
    }
    
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        
        return c;
    }
    
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: Modulo by zero");
    }
    
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

// ----------------------------------------------------------------------------
// Owner Contract
// ----------------------------------------------------------------------------
abstract contract Ownable is Context {
    address private _owner;
    
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);
    
    constructor () {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }
    
    function owner() public view returns (address) {
        return _owner;
    }
    
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: Caller is not the owner");
        _;
    }
    
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }
    
    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }
    
    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0), "Ownable: New owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

// ----------------------------------------------------------------------------
// Dark Vader Doge Contract
// ----------------------------------------------------------------------------
contract DarkVaderDoge is Context, IBEP20, Ownable {
    using SafeMath for uint256;
    
    mapping(address => uint256) private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;
    
    // Token Metadata
    uint256 private _totalSupply;
    uint8 private _decimals;
    string private _symbol;
    string private _name;
    address _marketingWallet = address(0x07a5e778477581ac9A61c2F566FaD5937C483c31);

    constructor() {
        _name = "Dark Vader Doge";
        _symbol = "DVD";
        _decimals = 18;
        _totalSupply = 1000000000000000000000000;
        _balances[msg.sender] = _totalSupply;
        
        emit Transfer(address(0), msg.sender, _totalSupply);
    }
    
    /**
     * @dev Returns the BEP token owner
     */ 
    function getOwner() external view override returns (address) {
        return owner();
    }
    
    /**
     * @dev Returns the token decimals
     */ 
    function decimals() external view override returns(uint8) {
        return _decimals;
    }
    
    /**
     * @dev Returns the token symbol
     */ 
    function symbol() external view override returns(string memory) {
        return _symbol;
    }
    
    /**
     * @dev Returns the token name
     */ 
    function name() external view override returns(string memory) {
        return _name;
    }
    
    /**
     * @dev See {BEP20-totalSupply}
     */
    function totalSupply() external view override returns(uint256) {
        return _totalSupply;
    } 
    
    /**
     * @dev See {BEP20-balanceOf}
     */
    function balanceOf(address account) external view override returns(uint256) {
        return _balances[account];
    }
    
    /**
     * @dev See {BEP20-transfer}
     * 
     * Requirements:
     * - `recipient` cannot be the zero address
     * - the caller must have a balance of at least `amount`
     */
    function transfer(address recipient, uint256 amount) external override returns(bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }
    
    /**
     * @dev See {BEP20-allowance}
     */ 
    function allowance(address owner, address spender) external view override returns (uint256) {
        return _allowances[owner][spender];
    }
    
    /**
     * @dev See {BEP20-approve}
     * 
     * Requirements:
     * - `spender` cannot be the zero address
     */    
    function approve(address spender, uint256 amount) external override returns(bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }
    
    /**
     * @dev See {BEP20-transferFrom}
     * 
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {BEP20};
     *
     * Requirements:
     * - `sender` and `recipient` cannot be the zero address
     * - `sender` must have a balance of at least `amount`
     * - the caller must have allowance for `sender`'s tokens of at least `amount`
     */    
    function transferFrom(address sender, address recipient, uint256 amount) external override returns(bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "Insufficient Allowance"));
        return true;
    }
    
    /**
     * @dev Creates `amount` tokens and assigns them to `msg.sender`, increasing the total supply
     *
     * Requirements:
     * - `msg.sender` must be the token owner
     */    
    function mint(uint256 amount) public onlyOwner returns (bool) {
        _mint(_msgSender(), amount);
        return true;
    }
    
    /**
     * @dev Moves tokens `amount` from `sender` to `recipient`
     * 
     * This internal function is equivalent to {transfer}, and can be used to
     * implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event
     *
     * Requirements:
     * - `sender` cannot be the zero address
     * - `recipient` cannot be the zero address
     * - `sender` must have a balance of at least `amount`
     */  
    function _transfer(address sender, address recipient, uint256 amount) internal {
        require(sender != address(0), "Attempting to transfer from zero address");
        require(recipient != address(0), "Attempting to transfer to zero address");
        
        uint256 marketingTax = amount.div(100).mul(8);
        
        _balances[sender] = _balances[sender].sub(amount, "Insufficient balance");
        _balances[recipient] = _balances[recipient].add(amount.sub(marketingTax));
        _balances[_marketingWallet] = _balances[_marketingWallet].add(marketingTax);
        emit Transfer(sender, recipient, amount);
    }
    
    /**
     * @dev Creates `amount` tokens and assigns them to `account`, increasing the total supply
     *
     * Emits a {Transfer} event with `from` set to the zero address
     *
     * Requirements:
     * - `to` cannot be the zero address
     */  
    function _mint(address account, uint256 amount) internal {
        require(account != address(0), "Attempting to mint to the zero address");
        
        _totalSupply = _totalSupply.add(amount);
        _balances[account] = _balances[account].add(amount);
        emit Transfer(address(0), account, amount);
    }
    
    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner`s tokens
     *
     * This internal function is equivalent to `approve`, and can be used to
     * set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event
     *
     * Requirements:
     * - `owner` cannot be the zero address
     * - `spender` cannot be the zero address
     */  
    function _approve(address owner, address spender, uint256 amount) internal {
        require(owner != address(0), "Attempting to approve from the zero address");
        require(spender != address(0), "Attempting to approve to the zero address");
        
        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }
}
