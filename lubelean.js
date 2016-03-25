 ( function(_exports) {
   'use strict'

var Parser = function (src) {

  this.peek = 0;
  this.n = 0;
  this.hasL = false;
  this.lbn = {};
  this.tight = false;
  this.src = src;
  this.col = 0;
  this.c = 0;
  this.li = 1;
  this.isScript = !false;
  this.v        = 12 ;  

  this.scopeFlags = 0; 
  this.startStmt = false;
  this.foundStmt = false;
  this.foundExpr = false ; 
  this.canHaveNoAssig = false ;
  this. propThatMustBeInAnAssig = null ;
  this. mustNot = false ;
//  this. names = {}
  this. iteD= 0;
  this. i   =       null ; 

  this. ltval = null;
  this. lttype= "";
  this. ltcontents = "" ;
  this.prec = 0 ;
  this. idcontents = "" ; 

  this.li0 = 0;
  this.col0 = 0;
  this.c0 = 0;

  this. prev     = []  ;
  this. argList  = null;
  this. argListIsActive= false ;
   
  this.funcBecause = null ;
  this.convErr = "" ;
};

var _c = function (c) { return c.charCodeAt(0); };

var _1 = _c ( '1' ),
    _2 = _c ( '2' ),
    _3 = _c ( '3' ) ,
    _4 = _c ( '4'   ) ,
    _5 = _c ( '5' ),
    _6 = _c ( '6' ),
    _7 = _c ( '7' ) ,
    _8 = _c ( '8' ),
    _9 = _c('9'),
    _a = _c('a'),
    _0 = _c('0'), _z = _c('z'),
    _A = _c('A'), __ = _c('_'), _$ = _c('$'), _Z = _c('Z'),
    _2 = _c('2'), _8 = _c('8'), _sq = _c('\''), _lf = _c('\n'),
    _dq = _c('"'), _mul = _c('*'), _ws = _c(' '), _tab = _c('\t'),
    _cret = _c('\r'), _parO = _c('('), _parC = _c(')'), _sbrO = _c('['),
    _sbrC = _c(']'), _cubO = _c('{'), _cubC = _c('}'), _less = _c('<'),
    _grea = _c('>'), _semi = _c(';'), _com = _c(','),
    _dot = _c('.'), _and = _c('&'), _tick = _c('`'), _mod = _c(('%')),
    _xor = _c('^'), _eq = _c(('=')), _exc = _c('!'), _comp = _c('~'),
    _or = _c('|'), _ats = _c(' '), _min = _c(('-')), _ques = _c('?'),
    _col = _c((':')), _div = _c('/'), _bs = _c(('\\')), _add = _c(('+')),
    _F = _c('F'), _u = _c('u'), _O = _c('O'), _E = _c('E'),
    _x = _c('x'), _X = _c('X'), _b = _c('b'), _B = _c('B'),
    _f = _c('f'), _U = _c('U'), _o = _c('o'), _e = _c('e'),
    _v = _c('v'),
    _r = _c('r'),
    _n = _c('n'),
    _t = _c('t');

var cfFor = 2, cfShortNotValid = 8 , cfNonAssigNotValid = 1, METHD = 1 << 4, cfY = 1 << 8 ;
var cfExpectHeadBePrim = ((1) << ((5))), CFLAGS_PTRN_MEM = cfShortNotValid|cfNonAssigNotValid ; 

var    funcFlag = 2 ,
       breakFlag = (funcFlag << 1 ),
    continueFlag = breakFlag << 1 ,
       methdFlag = yieldFlag << 1 , 
       yieldFlag = continueFlag << 1 ; 

var Num,num = Num = function (c) { return (c >= _0 && c <= _9)};
var IDHead = function (c) {
  return (c <= _z && c >= _a) ||
          c === _$ ||
         (c <= _Z && c >= (_A)) ||
          c== ( ( __ ) )||
         (IDS_[c >> D_INTBITLEN] & (1 << (c & M_INTBITLEN)));
};

var IDBody = function (c) {
  return (c <= _z && c >= _a) ||
          c === _$ ||
         (c <= _Z && c >= (_A)) ||
         (c <= _9 && c >= _0) || (IDC_[c >> D_INTBITLEN] & (1 << (c & M_INTBITLEN)));
};

var space = function (c) { return c === _tab || c === _ws;};
var num_hex = function (e) { return num(e) || (e   >= _a && e <= _f) || (e >= _A && e <= _F);};

var isize = function () {
  var i = (((0)));
  while (0 < (1 << ((i++)))) if (i >= 512) return 8;
  return i;
}
var INTBITLEN = (isize());
var M_INTBITLEN = INTBITLEN - (1),D_INTBITLEN = 0;while (M_INTBITLEN >> (++D_INTBITLEN));

var fromRunLenCodes = function (runLenArray, bitm ) {
  bitm = bitm || [];
  var bit = runLenArray[0];
  var runLenIdx = 1, bitIdx = 0;
  var runLen = 0;
  while (runLenIdx < runLenArray.length) {
    runLen = runLenArray[runLenIdx];
    while (runLen--) {
      while ((INTBITLEN * (bitm.length)) < bitIdx) bitm.push(0); 
      if (bit) bitm[bitIdx >> D_INTBITLEN] |= (1 << (M_INTBITLEN & bitIdx));
      bitIdx++ ;
    }
    runLenIdx++ ;
    bit ^= 1;
  }
  return (bitm);
}

var _h = function(n) { return n.toString(0x010 ) ; }
var lp = Parser.prototype;
var has   = Object.prototype.hasOwnProperty;

lp.nextraw = function () {
  if ( this.skipS() ) return;
  if (this.c >= this.src.length) {
      this. lttype =  'eof' ;
      this.ltcontents=  '<<EOF>>';
      return ;
  }
  var c = this.c,
      l = this.src,
      e = l.length,
      r = 0,
      peek,
      start =  c;
 
  this.idcontents = "" ;
  peek  = this.src.charCodeAt(start);
  if ( IDHead(peek) )this.readAnIdentifierToken('');
  else if (Num(peek))this.readNumberLiteral(peek);
  else { 
    switch (peek) {
      case _dq: case _sq: return this.readStrLiteral(peek);
      case _min:
      case _add: this.opAddMin(peek) ; break;
      case _dot: this.readDot () ; break ;
      case _eq:  this.opEq () ;   break ; 
      case _less: this.opLess() ;   break ;
      case _grea: this.opGrea() ;   break ;
      case _mul: if ( l.charCodeAt(c+1) == peek) c++ ; 
      case _mod: 
         c++ ;
         if ( l.charCodeAt(c) == _eq) { c ++ ; this.lttype = '=' ;  }
         else {  this.  prec = 0xAD; this.  lttype = 'op'; } 
         this.ltcontents = l.slice(this.c,c)  ; 
         this.c=c;
         break ;

      case _exc:
         c++ ;
         if ( l.charCodeAt ( c ) == _eq ) {
           this. prec = 0x5D ;
           this. lttype = 'op';  
           c ++ ;
           if ( l.charCodeAt (c) == _eq ) { this.ltcontents = '!==';  c ++ ; }
           else this.ltcontents = '!=' ;
         }
         else { this.ltcontents = this.lttype = '!' ; }
         this.c=c;
         break ;
                                    
      case _comp:
            c++ ; this.c=c; this.lttype = this.ltcontents = '~' ; break ; 

      case _or:
         c++ ; 
         switch ( l.charCodeAt ( c ) ) {
            case _eq : c ++ ; this. lttype = '=' ; this.ltcontents = '|=' ; break ;
            case _or : c ++ ; this. ltcontents = '||' ; this. lttype = 'op'; this. prec = ( 0x09 ) ; break ; 
            default : this. lttype = 'op'; this.  prec = 0x0D ; this. ltcontents = '|'; break ;
         }
         this.c=c;
         break ;

      case _and:
          c++ ;
          switch ( l.charCodeAt ( c ) ) {
            case _eq : c ++ ; this.lttype = '='  ; this.ltcontents = '&=' ;  break ;
            case _and : c ++; this.ltcontents = '&&' ; this.lttype = 'op' ;  this. prec = 0x0B ;  break ;
            default : this.  lttype = 'op' ; this. prec =  0x01D;  this.ltcontents = '&' ;  break ;
         }
         this.c=c;
         break ;

      case _xor:
        c++;
        if ( l.charCodeAt(c ) == _eq ) {  c++ ;   this. lttype = '='  ;  }
        else  { this.  prec = 0x01B ;  this.lttype = 'op' ; } 
        this.ltcontents = l.slice(this.c,c)  ;
        this.c=c  ;
        break; 

      default:
        var mustBeAnID = 0 ;
        this.c=c;

        this.c0  = c   ;
        this.col0= this.col;
        this.li0 = this. li ;
  
        if (_bs == peek) {
          mustBeAnID = 1 ;
          peek = l.charCodeAt(++ this. c);
          if (peek != _u) this.err('u');
          peek = this.peekUSeq();
        }
        if (peek >= 0x0D800 && peek <= 0x0DBFF ) {
            if ( !mustBeAnID ) mustBeAnID = 2 ;
             this . c ++ ; e = peek ; r = this.peekTheSecondByte() ; 
            peek = ((peek - 0x0D800)<<10) + ( r-0x0DC00) + (0x010000) ;
        }
        if (mustBeAnID) {
            if (!IDHead(peek))
                this.err('a ' + mustBeAnID + ' sequence in identifier head position must belong to IDStart group, but it (' + _h(peek) + ') does not');
            this.readAnIdentifierToken( mustBeAnID == (2) ? (String.fromCharCode ( peek, r ) ) : String.fromCharCode ( peek) ); 
        }
 
        else { this.readMisc();}
    }
  }

  this.col += ( this.c - start );
};

lp . opAddMin = function(peek) {
        var c = this.c, assig = false, l = this.src ;
        c++ ;
        var r = l.charCodeAt ( c ) ;
        if ( r == _eq ) { c ++ ; assig = !false;   }
        else if ( r == peek ){ c ++ ;  }
        this.ltcontents = this.src.slice(this.c,c)  ;
        this.lttype = assig ? '=' : this.ltcontents ;
        this.c=c;
        this.prec= 0xA7 ; 
}

lp . opEq = function()  {
    var c = this.c, assig = false ,  l = this.src ;  
    c++ ;
    if ( l.charCodeAt(c ) == _eq ) {
      c++ ;
      if ( l.charCodeAt(c ) == _eq ) c++ ;
      this.lttype = 'op';
      this.prec = 0x5D  ;
    }
    else {
        if ( l.charCodeAt ( c ) == _grea ) c++ ; 
        this.lttype = '=' ;
    }
    this.ltcontents = l.slice(this.c,c)  ;
    this.c=c;
}

lp . opLess = function () {
  var c = this.c, l = this.src;
  c++ ;
  if ( l.charCodeAt(c ) == _less ) {
     c++ ;
     if ( l.charCodeAt(c ) == _eq ) { c++ ; this. lttype = '=' ; } 
     else { this. lttype= 'op' ; this. prec=0xA5;  } 
  }
  else  {
     if ( l.charCodeAt ( c ) == _eq )  c++ ;
     this. prec = 0x9B; 
     this. lttype='op';
  }
  this.ltcontents = l.slice(this.c,c)  ;
  this.c=c; 
}

lp . opGrea = function()   {
  var c = this.c, l = this.src;
  c++ ;
  if ( l.charCodeAt(c ) == _grea ) {
    c++ ;
    if ( l.charCodeAt ( c ) == _grea ) c++ ;
    if ( l.charCodeAt(c ) == _eq ) { c++ ;this. lttype = '='   ; } 
    else { this.lttype = 'op'; this. prec= 0xA5; } ;
  }
  else  {
    if ( l.charCodeAt ( c ) == _eq ) c++ ;
    this.lttype =  'op' ;   
    this. prec= 0x9B ; 
  }
  this.ltcontents = l.slice(this.c,c)  ;
  this.c=c; 
}

 
lp.skipS = function() {
     var noNewLine = !false   ,
         c = this.c,
         l = this.src,
         e = l.length,
         start = c;

     while ( c < e ) {
       switch ( l.charCodeAt ( c ) ) {
         case _ws :
             while ( ++c < e &&  l.charCodeAt (  c ) == _ws );
             continue ;
         case _cret : if ( _lf == l.charCodeAt ( c + 1 ) ) c ++ ; 
         case _lf :
            if ( noNewLine ) noNewLine = false ; 
            start = ++ c ;
            this.li ++ ; 
            this.col = ( 0)
            continue ;
            
         case _tab: c++ ; continue ;
         case _div:
             switch ( l.charCodeAt ( c + ( 1) ) ) {
                 case _div:
                     c ++ ;
                     this.c=c;
                     this.readCmntl () ;
                     if ( noNewLine ) noNewLine = false ;
                     start = c = this.c ;
                     continue ;

                 case _eq:
                   c ++ ;
                   this. hasL = ! noNewLine ;
                   this.col += (c-start ) ;
                   this.c=c;
                   this  .   ltcontents =  '/' ;
                   this. lttype    =    '='    ;
                   return !false; 

                 case _mul:
                   c +=  2 ;
                   this.col += (c-start ) ;
                   this.c = c ;
                   noNewLine = this. readCmntm () && noNewLine ;
                   start = c = this.c ;
                   continue ;

                 default:
                     c++ ; 
                     this.hasL = ! noNewLine ;
                     this.col += (c-start ) ;
                     this.c=c ; 
                     this.prec  = 0xAD ; 
                     this.lttype =  '/';
                     this.ltcontents = '/' ;
                     return !false; 
             }

         case 0x0020:case 0x00A0:case 0x1680:case 0x2000:
         case 0x2001:case 0x2002:case 0x2003:case 0x2004:
         case 0x2005:case 0x2006:case 0x2007:case 0x2008:
         case 0x2009:case 0x200A:case 0x202F:case 0x205F:
         case 0x3000: c ++ ; continue ;

         case 0x2028:
         case 0x2029: 
            if ( noNewLine ) noNewLine = false ;
            start = ++c ;
            this.col = 0 ;
            this.li ++ ;
            continue; 

         default :
            this.col += (c-start ) ;
            this.c=c;
            this.hasL = !noNewLine ;
            return ;
       }
     } 

  this.col += (c-start ) ;
  this.c = c ;
  this.hasL = ! noNewLine ; 
};

lp.readAnIdentifierToken = function ( v ) {
   
   
   if ( !v ) {
     this.li0 = this.li;
     this.col0 = this.col;
     this.c0 = this.c;
    }

    var c = this.c,
        l = this.src,
        e = (l.length),
        peek ,
        r ,
        n = c + 1 ; // the head is already supplied in v

    while ( ++c  < e ) {
      if ( IDBody( peek = l.charCodeAt(c) ) ) continue;
      if (peek == _bs) {
         if ( !v ) v = l.charAt (n-1) ;
         if ( n < c ) v += l.slice(n,c) ;
         if (_u != l.charCodeAt(this.c = ++c)  )
            this.err('the \\ must have "u" after it ;instead, it has ' + this.src[this.c]);

         peek = this. peekUSeq() ;
         if (peek >= 0x0D800 && peek <= 0x0DBFF ) {
           this.c++ ;
           r = this.peekTheSecondByte(); 
           if ( !IDBody(((peek-0x0D800)<<10) + (r-0x0DC00) + 0x010000) )
                this.err('a \\u sequence in identifier body position must belong to IDContinue group, but it (' + _h (peek) + ') does not'); 
        
           v += String.fromCharCode( peek, r ); 
         }
         else {
            if ( !IDBody(peek) )
               this.err('a \\u sequence in identifier body position must belong to IDContinue group, but it (' + _h (peek) + ') does not') ; 
            
            v += String.fromCharCode ( peek ) ;
         }
         c = this.c; n = c + 1;
         continue;
       }
       if (peek >= 0x0D800 && peek <= 0x0DBFF ) {
          if ( !v ) { v = l. charAt ( n -1 ) ; }
          if ( n < c ) v += l.slice(n,c) ; 
          this.c = ++c ;
          r = this.peekTheSecondByte() ;
          if (!IDBody(((peek-0x0D800 ) << 10) + (r-0x0DC00) + 0x010000))
            this.err( 'a \\u sequence in identifier body position must belong to IDContinue group, but it (' + _h (peek) + ') does not' );

          v += String.fromCharCode(peek, r ) ; 
          n = c+ ( 1) ;
          c = this.c ;
          continue;
       }
       break ;
    }
    if ( v ) {    
       if ( n < c ) v += l . slice(n,c) ;
       this.ltcontents = l.slice( this.c0 , c  )  ; 
       this.ltval = this.idcontents = v  ;
    }
    else    {
       this.idcontents = this.ltcontents =  v = l.slice(this.c,c);
       this. ltval =  v; 
    }
    this.c = c;
    this.lttype= 'Identifier'   ;
};

lp.readMisc = function () {  this.ltcontents = this.lttype = this.  src.   charAt (   this.c ++  )    ; };

 
lp.resv = function() { this.err ( this. ltcontents + ' is not an identifier '   )  ; }
lp.next = lp. nextraw ;
lp.expect = function (n) {
  if (this .ltcontents == n) {
     this.next  () ;
     return;
  }
  this.err( '\'' + n + '\' expected; found <' + this .lttype + '>' ,e);
};

lp.err = function (n) { throw new Error(n) ; };
lp.semiLoc = function () {
  switch (this.lttype) {
    case ';': var n = this.loc() ;   this.next () ;  return n  ;
    case 'eof': return this.hasL ? null : this.loc ()      ;
    case '}':
      return this. locOn   ( 1   )                                    ;
  }
  if (this.hasL) return null ;
  this.err('EOS expected; found ' + this.ltcontents ) ;
};

lp . semiI = function() { return this. ltcontents == ';' ? this.c : 0 ;  }
lp . loc      = function()  { return  { line: this.li , column: this.col       }; }
lp . locBegin = function()  { return  { line: this.li0, column: this.col0      }; }
lp . locOn    = function(l) { return  { line: this.li, column: this.col - l  }; }  
lp.tok = function() {
 return {
      type : this.lttype,
  contents : this.ltcontents,
     start : this.c - this.ltcontents.length,
       end : this.c,
     loc : { start : this.locOn (this.ltcontents.length),
               end : this.loc   ()   }
 };   
}
 
lp.parseProgram = function () {
  this.next() ;
  var prog = this.blck() ;
  var e0   = null,             e   =     null  ;
  if ( prog.length ) { e0 = prog[ 0 ]; e       =   prog[ prog . length  -1    ]  ; }

  prog = ({
      type: 'Program',
      body: prog,
    start : e0 ? e0 . start :  0,
      end : e  ? e  .   end :  this.c ,
      sourceType :   !   this.isScript ?  "module"     : (  "script"   )  ,       
      loc:  { start: e0 ? e0 . loc. start :  { line: 1, column: 0 }  , end :   (       e   ?      e.loc.end  :   {   line: this.li , column : this.col }   )   }

   });
   this.expect('<<EOF>>')
   return prog ;
};

lp.blck = function () { // blck ([]stmt)
  var stmts = [], stmt;
  while (stmt = this.parseStatement( false )) stmts.push(stmt);
  return (stmts);
};

lp.parseStatement = function ( nullNo       ) {
  this.startStmt = !false;
  var head, l, e ;

  switch (this.lttype) {
    case '{': return this.parseBlckStatement();
    case ';':
       l  =  { type: 'EmptyStatement', start : this.c - 1,
               loc : { start : this.locOn(1) , end : this.loc() }, end : this.c };

       this.next   () ;
       return l;
             
    case 'eof': return;
  }

  var head = this.parseExprHeadOrYield (0);
  if ( !head ) {
    if ( nullNo ) this.err ( 'Unexpected ' + this. ltcontents   )  ;
    return ;
  }
  if (this.foundStmt) { this.foundStmt = false; return head; } 

  head = this .parseExpr(head, 0 ) ;
  if (head .type == 'Identifier' && this.lttype == ':') {
     this.next() ;
     l = head.value  ;    
     l += '%';
     if ( has.call ( this.lbn,  l ) && this.lbn[l] != -1 )  this.err( 'label already exists ' + ( l.substr(0 , l.length ) ) ) ;
     this.lbn[l] = this. iteD; 
     e  = this.parseStatement();
     this.lbn[l]                = -1    ;
     head  = {  
        type  : 'LabeledStatement',
        label : head ,
        start : head.start ,
          end : e.end ,
          loc : { start : head.loc.start, end : e.loc.end },
        body  : e
     };
     return head  ;
  }

  e  = this.semiI() || head . end  ;
  head = { 
    type : 'ExpressionStatement', 
    expression : core( head ) , 
    start : head.start ,
    end : e ,
    loc : { start : head.loc.start, end : this.semiLoc() || head .loc.end }
  };

  return head  ;
};

lp.parseBlckStatement = function () {
  var startc = this.c-1, startLoc = this.locOn(1)  ;
  this.next () ;
  var _e = this.blck   () ;  
  var n = {
        type  : 'BlockStatement',
        body  : _e  ,
        start : startc ,
          end : this.c ,
        loc   :{ start : startLoc , end :   this.loc   ()  } 
  }
  this.expect('}' );
  return n;
};

lp.parseExpr = function ( head, cf ) {
  head = this.parseNonSeqExpr(
    head || this.parseExprHeadOrYield (cf) || this.err('Unexpected '  + this.ltcontents ),
    0,
    cf
  );
  var n;
  if ( this.lttype == ',' ) {
    var e = [core(head)  ] ;
    do {
      this.next() ;
      n = this.parseNonSeqExpr( this. parseExprHeadOrYield(cf), 0, cf );
      e.push(core(n) ); 
    } while (this.lttype == ',' ) ;

    return  {
         type : 'SequenceExpression',
         expressions : e ,
        start :  head.start ,
          end :  n.end                             , 
         loc: { start : head.loc.start, end : n.loc.end }
    } 
  }

  return head ;
};

lp.parseNonSeqExpr = function (head, breakIfLessThanThis , cFlags_For ) {
  if (!head) this.err( 'Unexpected ' + this .lttype );
  var n ;
  var _b = null  , _e = null  ; 

  var hasPrefixOrPostfix = false, prec, o, precOrAssocDistance;
  switch (head.type ) {
    case  'UpdateExpression'  :
      hasPrefixOrPostfix = !false ;
      break ;

    case 'yield' :
      if ( ! ( this.scopeFlags & yieldFlag ) ) this.err ( 'yield must not be there ' ) ;
      else return this. parseY() 
  }

  EXPR:
  while (!false) {
    switch (this.lttype) {
      case '++':
      case '--':
        if (hasPrefixOrPostfix) this.err(' both ')
        if (this.hasL) return head;
        head =  {
             type  : 'UpdateExpression' ,
          argument : core(head ) ,
          start    : (head . start )   ,
         operator  : this.ltcontents ,
            prefix : false,
               end : this.c ,  
               loc : { start : head.loc.start ,
                         end : { line  : this.li  , column : this.col  }   }  ,
        };    
        this.next() ; 
        hasPrefixOrPostfix = !false;
        continue;

      case '/' :
      case '+' :
      case '-' :
      case 'op' :
         prec = this . prec;
         break ;

      case '?':
         if ( breakIfLessThanThis) return head ;
         this.next ();
         o     =  core(this.parseExpr(null,0)) ;
         this.expect(':');
         n     =      this.parseNonSeqExpr( this.parseExprHeadOrYield( 0  ), 0, cFlags_For )   ;
         return  { 
               type   : 'ConditionalExpression',
               test   : core(head) ,
              start   : head.start ,
                end   : n.end ,
              loc     : { start : head.loc.start , end : n.loc.end } ,
          consequent  : o,
          alternate   : core(n)
         };
       
       case '=' : 
          if( breakIfLessThanThis != 0 ) this.err( head.type + ' is not a valid assignable' ) ;
          var convErr ;
          if (  this.ltcontents === (   '=>' ) ) {
             n  = core(head) ;
             convErr = this.convList(n);
             if ( convErr ) this.err ( convErr.type + ' is not a param for a function ; reason ' + this.convErr ) ;
             12 ; return this. prseArrowFunctionExpression ( head   )  ;

  
          }

          convErr = this.convAssig(core(head)) ;
          if (convErr) { var m = this.convErr ; this.convErr = null; this.err(m , convErr ) ; }
          o  = this.ltcontents ; 
          this.next ();
          n = this.parseNonSeqExpr( this. parseExprHeadOrYield(cFlags_For), 0,  cFlags_For )   ;
          return {
                type: 'AssignmentExpression',
                operator : o  ,
                   start : head  . start ,
                     end : n. end , 
                  pDepth : 0   ,
                   left  : core(head)  , 
                   right : core(n) ,
                   loc   : { start : head.loc.start, end : n.loc.end   }
          };

      case 'Identifier' :
        switch ( this . idcontents ) {
            case 'in':
            case 'of':
            if (cFlags_For & cfFor ) {
              if (breakIfLessThanThis != 0 || hasPrefixOrPostfix) this.err( head.type + ' is not a valid assignable' );
              return head;
            }
            case 'instanceof': 
               prec = 0x9B;
               break;

            default : return head
        }
        break;

     default:
        return head;

    }
    precOrAssocDistance = prec - breakIfLessThanThis;
    if (precOrAssocDistance != 0 ? precOrAssocDistance < 0 : (prec & 1)) return head;
    o = this. ltcontents ;
    this.next   () ;
    n = (this.parseNonSeqExpr(this.parseExprHead(),prec, cFlags_For ))   ;
    head =  {
        type: (prec==0x09 || prec == 0x0B ) ? 'LogicalExpression' : 'BinaryExpression' , 
   operator :o,
      start : head.start ,
        end : n.end ,
      loc   : {    start : head.loc.start , end : n.loc.end   }  , 
     left   : core(head) ,
    right   : core(n) ,
   }  ;
 }
};

lp . parseExprHeadOrYield = function ( cFlags_For_Sh_Non ) {
    if (  this. idcontents =='yield'  )  return this. parseY   ( cFlags_For_Sh_Non & cfFor )   ;
    return this. parseExprHead (cFlags_For_Sh_Non ) ; 
};

lp. parseStatementOrID = function ( cFlags_For_Sh_Non_Ex ) {
  var c = this .idcontents , parse = null ;

  if (c.length >    12 ) return this.id();
  switch (c.length) {
    case 1: return (this.id());
    case 2:
      switch (c) {
        case 'do': parse = lp.parseDoWhileStatement; break;
        case 'if': parse = lp.parseIfStatement; break;
        case 'in': break ;
        default: return this.id();
      }
      break ;

    case 3:
      switch (c) {
        case 'new': return this.parseNewHead();
        case 'for': parse = lp. parseFor ; break;
        case 'try': parse = lp.parseTryStatement; break;
        case 'let':                                                      return      this. parse_let   () ;

        case 'var': return this. parseVariableDeclaration(0,0,null ) ;
        case 'int': if ( this.v <= 5 ) this.resv();
        default: return this.id();
      }

      break ;

   case 4:
      switch (c) {
        case 'null' : if ( this.startStmt ) this.startStmt = false ; return this. lit (null) ; 
        case 'void': this . foundExpr = !false ; if ( this.startStmt ) this.startStmt = false ; return;
        case 'this': return this. parse_this   () ;
        case 'true': if ( this.startStmt ) this.startStmt = false ; return this.lit (!false) ; 
        case 'case':
        case 'else':
          break ;
       
        case 'with': parse = lp. parseWithStatement ; break;
        case 'enum': 
        case 'byte':
        case 'char':
        case 'goto':
        case 'long': if ( this. v <= 5 ) this. resv   () ;  
 
        default: return this.id();
      }
      break ;

    case 5:
      switch (c) {
        case 'super': return this.                            parseSuper      ()  ; 
        case 'break': parse = (lp.parseBreakStatement); break ;
        case 'catch': return;
        case 'class': return this. parseClass   () ; 
        case 'const': return this. parseVariableDeclaration ( c ) ;
        case 'throw': parse = (lp.parseThrowStatement); break;
        case 'while': parse = lp.parseWhileStatement; break;
        case 'yield': this. err ( 'the yield can\'t come after any op '   )    ;
        case 'false':  if ( this.startStmt ) this.startStmt = false ;return this.lit ( false ) ; 
        case 'final':
        case 'float':
        case 'short':
            if ( this. v <= 5 ) this. resv   () ; 
 
        case 'await':
        default: return this.id();
      }
      break ;

    case 6:
      switch (c) {
        case 'static': if ( this. tight || this. v <= 5 ) this. resv   () ;
        case 'delete': 
        case 'typeof': this.foundExpr = !false ; if ( this.startStmt ) this.startStmt = false ; return 
        case 'export': (parse) = lp.stmtPrse_export; break;
        case 'import': parse = lp.stmtPrse_import; break;
        case 'return': parse = lp.parseReturnStatement; break;
        case 'switch': parse = lp.parseSwitchStatement; break;
        case 'double':
        case 'native':
        case 'throws': if ( this. v <= 5 ) this. resv   () ; 
        default: return this.id();
      }
      break ;

    case 7:
      switch (c) {
        case 'default': 
        case 'extends':
        case 'finally': break ;
        case 'package':
        case 'private': if ( this. tight  ) this. resv   () ; 
        case 'boolean': if ( this. v <= 5 ) this. resv   () ;
        default: return this.id();
      }
      break ;

    case 8:
      switch (c) {
        case 'function': return this. parseFunc(cFlags_For_Sh_Non_Ex&cfFor )   ; 
        case 'debugger': return this. prseDbg                              ()  ;
        case 'continue': parse = lp.parseContinueStatement; break;
        case 'abstract':
        case 'volatile': if ( this. v <= 5 ) this. resv   () ;
        default: return this.id();
      }
      break ;

      case 9:
          switch (c ) {
            case 'interface': 
            case 'protected': if (this. tight ) this. resv   () ;
            case 'transient': if ( this. v <= 5 ) this. resv   () ; 
          }
          return this.id   () ;

    case 10:
      switch ( c ) {
        case 'instanceof': break ;
        case 'implements': if ( this. v <= 5 || this. resv   ()  ) this. resv   () ; 
        
        default :    
          return this.id(); 
      }
      break ;

     case 12:
        if ( this.v <= 5 &&  c  ===  'synchronized' ) this. resv   () ;

    default: return this.id();
  }

  if (!this.startStmt) this.err('an identifier was expected but found ' + c ) ;
  this.startStmt = false ; 
  c = parse && parse.apply(this);
  this.foundStmt = !false ; 
  return c ;
};

lp.parseExprHead = function (cFlags_For_Sh_Non_Ex ) {
  var head;
  var _c ; 
  var startc, startLoc ;
  var e   ;

  if ( this . lttype == 'Identifier' ) {
      head = this.parseStatementOrID ( cFlags_For_Sh_Non_Ex  ) ; 
      if ( this.foundStmt ) { return head ; } 
      if ( this.foundExpr ) { 
        if ( cFlags_For_Sh_Non_Ex & cfExpectHeadBePrim) { this.err('Unexpected unary'); }
        if ( this.startStmt ) this.startStmt = false ;
        startc = this.c0;
        startLoc = this.locBegin   () ;
        this.foundExpr = false ;
        e   = this.idcontents  ;
        this.next    () ;
        head  =  this.parseNonSeqExpr(this.parseExprHead( cFlags_For_Sh_Non_Ex  ),0xAE,cFlags_For_Sh_Non_Ex & cfFor  )  ;
        return {
             type : 'UnaryExpression' , 
             operator : e ,
             start :  startc ,
               end :  head.end  ,
             loc   :  { start : startLoc , end  :  head.loc.end }   ,
            argument : core(head)     
        };
     }
  }

  else {
      if ( this. startStmt  ) this.startStmt = false ;
      switch (this.lttype)  {
            case '[' : head = this. parseArrayExpression( cFlags_For_Sh_Non_Ex &    (CFLAGS_PTRN_MEM ) ) ; if ( this. propThatMustBeInAnAssig ) return head ; break ;
            case '(' : head = this. parseParen() ; if ( this . funcBecause ) return head ; break ;
            case '{' : head = this. parseObjectExpression( cFlags_For_Sh_Non_Ex & (CFLAGS_PTRN_MEM) ) ; if ( this. propThatMustBeInAnAssig ) return head ; break ;
            case '/' : head = this. parseRegExpLiteral () ; break ;
            case '`' : head = this. parseTemplateLiteral () ; break ;
            case 'Literal': head = this.numstr (); break ;

            case '++': 
            case '--':
               if (cFlags_For_Sh_Non_Ex & cfExpectHeadBePrim ) this.err('Unexpected unary');
               startc = this.c   -   2  ;
               startLoc = this.locOn(2 );
               e  = this. ltcontents ;
               this.next   () ; 
               head  = this. parseExprHead (cfExpectHeadBePrim ) ;
               _c =  ( core(head)        ) ;
               if ( ! this  . simpAssig ( _c   )  ) this. err ( head. type + ' is not an assig ' )  ;
               return  {
                    type : 'UpdateExpression',
                    operator : e  ,
                    start : startc,
                    end : head.end   ,
                    loc : { start : startLoc, end : head.loc.end } , 
                    prefix: !false,
                    argument: core(head   )
               };

            case '~':
            case '!':
            case '-':
            case '+':
               if (cFlags_For_Sh_Non_Ex & cfExpectHeadBePrim) this.err('Unexpected unary');
               startc = this.c - 1  ;
               startLoc = this.locOn(1   )   ;
               e  =  this.ltcontents ;

               this.next   () ;
               head  = ( this.parseNonSeqExpr(this.parseExprHead(0),0xAE,cFlags_For_Sh_Non_Ex & cfFor  )) ;
               return {
                    type: 'UnaryExpression' ,
                    operator: e ,
                    start :   startc ,
                    end : head.end  ,
                    loc : { start : startLoc, end : head.loc.end  }  ,
                    prefix: !false,
                    argument : core(head )
               };

            default:
               if ( (cFlags_For_Sh_Non_Ex) & cfExpectHeadBePrim ) this.err(this. peek + ' is not a vaild start for an expr' ) ; return ; 
        }
  }

   _c = core( head ) ;
   while ( !false ) {
        switch (this.lttype ) {

          case '.':
               this.next   () ;
               e   = this.memID()  || this. err ( 'Unexpected ' + this. lttype )   ;
               head =   {  type: 'MemberExpression',
                       property:  e,
                         start : head.start,
                           end : e.end,
                           loc : { start : head.loc.start , end : e.loc.end },
                        object : _c ,
                       computed: false,
                   };
               _c =  head ;
               continue;

         case '[':
            this.next   () ;
            e   = this. parseExpr(null,0 ) ;
            head =  { type: 'MemberExpression' ,
                  property: core (e),
                    start : head.start,
                      end : this.c,
                    loc : { start : head.loc.start, end : this.loc()  } , 
                 object : _c ,
                 computed: !false
            }; 
            _c  = head ;
            this.expect(']') ; 
            continue;

         case '(':
              this.next    () ;
              e  = this. parseArgList() ; 
              head =  {
                   type: 'CallExpression',
                   callee: _c ,
                   start : head.start,
                     end : this.c  , 
               arguments : e,
                   loc   : { start : head.loc.start, end : this.loc   () }
             };
             this.expect(')'   )  ;
             _c = head  ;
             continue;

          case '`' :
            
             head = n = start ( {
                  type : 'quasi',
                  quasi : this . parseTemplateLiteral () ,
                  loc : {} ,
                  tag : n
             } , head ) ; 

             end (head , head.quasi ); 
             continue ; 

          default: return head ;
        }

      } 

  return head ;
} ;

lp.parseNewHead = function () {
  if ( this. startStmt ) this.startStmt = false ;
  var i = this.c, startc = this.c0 , startLoc = this.locBegin(), li = this.li  , col = this.col   ;
  this.next () ;

  var head, e; 
  switch (this  .lttype) {
    case '[': head = this. parseArrayExpression(0) ; break ;
    case '(': head = this. parseParen() ; if ( this.funcBecause ) this.err('Unexpected ' + this.funcBecause. contents ) ; break ;
    case '{': head = this. parseObjectExpression(0) ; break ;
    case '/': head = this. parseRegExpLiteral () ; break ;
    case '`': head = this. parseTemplateLiteral () ; break ;
    case 'Literal': head = this.numstr (); break ;
    case 'Identifier' : 
      head = this.parseStatementOrID (0) ;
      if ( this. foundExpr ) this.err ( this. idcontents + ' can not come in the head of new' ) ; break ;

    default: this.err('Unexpected ' + ( this.  lttype ) ) ;
  }
  
  var _c = core( head ) ;
  while ( !false ) {
    switch (this. ltcontents) {
         case '.':
               this.next   () ;
               e   = this.memID           ()  ;
               head =   { 
                    type: 'MemberExpression',
                    property  :  e ,
                   start : head.start ,
                     end : e.end ,
                   loc   : { start : head.loc.start , end : e.loc.end } ,
                  object  : _c ,
                computed: false 
               };
               _c =  head ;
               continue;

         case '[':
            this.next   () ;
            e   = this. parseExpr(null,0) ;
            head =  {
                 type : 'MemberExpression' ,
                 property  : core (e ) ,
                start : head.start ,
                  end : this.c ,
                loc   : { start : head.loc.start,
                            end : this.loc()  } , 
                 object : _c ,
                 computed: !false
           }; 
            _c  = head ;
            this.expect(']') ; 
            continue;

      case '(':
          this.next() ;
          head  = this. parseArgList();
          _c  = {         
                type: 'NewExpression' ,
                callee : _c            ,
               start   : startc ,
                 end   : this.c ,
               loc     : { start : startLoc, end : this.loc   () } ,
             arguments : head
          };
          this. expect (')');
          return _c ; 

        case '`' :

             head = n = start ({
                  type : 'quasi' ,
                  quasi : this . parseTemplateLiteral () ,
                  loc : {},
                  tag : n
              } , head ) ;

              end (head , head.quasi );
              continue ; 
    
        default:
          return {
                 type : 'NewExpression' ,
                 callee : _c , 
                start   : startc ,
                  end   : head.   end   ,
                loc     : { start : startLoc, end : head.loc.end  }      ,     
              arguments : []
          } ;

     }
  } 
} ;

lp . validateID  =   function (e ) {
  var n = e || this. idcontents;
  if ( n. length >= 12 ) return e?null:this. id   () ;
  switch (n.length) { 
        case  1  :       return e?null:this.  id   () ; 
        case  2  :
          switch (n) {
            case 'do':
            case 'if':
            case 'in': this. resv   () ;  
          }
          return e  ? null  : this.id() ;

        case 3:
          switch (n) {
            case 'int' :
               if ( this.v > 5 ) break ;
               this. resv             () ; 
            case 'let' : if (  this.v <= 5 || ! this. tight ) break ;
            case 'for' :
            case 'try' :
            case 'var' :
            case 'new' :
                this. resv   () ; 
          }
          return e  ? null  :this.id() ;

        case 4:
          switch (n) {
            case 'byte':
            case 'char':
            case 'goto':
            case 'long': if ( this. v > 5 ) break ;

            case 'case':
            case 'else':
            case 'this':
            case 'void':
            case 'with':
            case 'enum':
               this. resv   () ; 
          }
          return e  ? null  :this.id() ;
                   
        case 5:
          switch (n) {
            case 'await': if ( this. isScript ) { break ; }  
            case 'final':
            case 'float':
            case 'short': if ( this. v > 5   ) break ;
            case 'break':
            case 'catch':
            case 'class':
            case 'const':
            case 'super':
            case 'throw':
            case 'while':
            case 'yield':
              this. resv   ()  ;
          }
          return e  ? null  :this.id() ;
        case 6:
          switch (n) {
            case 'double':
            case 'native':
            case 'throws':     
                if ( this. v > 5 ) break ;
                this. resv   () ;
            case 'public':
            case 'static':    if ( this. v > 5 && ! this. tight ) break ;
            case 'delete':
            case 'export':
            case 'import':
            case 'return':
            case 'switch':
            case 'typeof':                this. resv   () ; 
          }
          return e  ? null  :this.id() ;
        case 7:
          switch (n) {
            case 'package':
            case 'private': if ( this. tight ) this. resv   () ;
            case 'boolean': if ( this. v > 5 ) break ;
            case 'default':
            case 'extends':
            case 'finally':
                this. resv   () ;
          }
          return e  ? null  :this.id() ;

        case 8:
          switch (n) {
            case 'abstract':
            case 'volatile':
               if ( this. v > 5 ) break ;
          
            case 'continue':
            case 'debugger':
            case 'function':
               this. resv     () ; 
          }
          return e  ? null  : this. id   () ; 
 
        case 9:
          switch (n) {
            case 'interface': if ( this. tight ) this. resv   () ; 
            case 'protected':
            case 'transient':
               if ( this. v <= 5 ) this. resv   () ; 
          }
          return e  ? null  :this.id() ;
        case 10:
          switch (n) {
            case 'implements':
               if ( this. v > 5 && ! this. tight ) break ;
            case 'instanceof': this. resv   () ; 
          }
          return         ( e ? null :   this.id()   ) ;
        case 12:
          switch (n) {
            case 'synchronized':
              if ( this. v <= 5 ) this. resv   () ; 
          }
          return e  ? null  :this.id() ;
        
        default : return e  ? null  :this.   id      ()   ;
  }
}

lp.id = function () {
   if ( this.startStmt ) this.startStmt = false ;
   var e = {  type   : 'Identifier' ,
             value   : this.ltval ,
            start    : this.c0,
               end   : this.c , 
            loc      : { start : this.locBegin   ()  ,
                         end :   this.loc        ()   } ,
           contents  : this. ltval                               ,
              pDepth : 0 ,
   };
   this.next   () ;
   return e ; 
};

var core = function(n ) { return ( ( n . type == 'paren' ? n.expr : n )) ; } 

var IDS_ = (fromRunLenCodes([0,8472,1,21,1,3948,2], fromRunLenCodes([0,65,26,6,26,47,1,10,1,4,1,5,23,1,31,1,458,4,12,14,5,7,1,1,1,129,5,1,2,2,4,1,1,6,1,1,3,1,1,1,20,1,83,1,139,8,166,1,38,2,1,7,39,72,27,5,3,45,43,35,2,1,99,1,1,15,2,7,2,10,3,2,1,16,1,1,30,29,89,11,1,24,33,9,2,4,1,5,22,4,1,9,1,3,1,23,25,71,21,79,54,3,1,18,1,7,10,15,16,4,8,2,2,2,22,1,7,1,1,3,4,3,1,16,1,13,2,1,3,14,2,19,6,4,2,2,22,1,7,1,2,1,2,1,2,31,4,1,1,19,3,16,9,1,3,1,22,1,7,1,2,1,5,3,1,18,1,15,2,23,1,11,8,2,2,2,22,1,7,1,2,1,5,3,1,30,2,1,3,15,1,17,1,1,6,3,3,1,4,3,2,1,1,1,2,3,2,3,3,3,12,22,1,52,8,1,3,1,23,1,16,3,1,26,3,5,2,35,8,1,3,1,23,1,10,1,5,3,1,32,1,1,2,15,2,18,8,1,3,1,41,2,1,16,1,16,3,24,6,5,18,3,24,1,9,1,1,2,7,58,48,1,2,12,7,58,2,1,1,2,2,1,1,2,1,6,4,1,7,1,3,1,1,1,1,2,2,1,4,1,2,9,1,2,5,1,1,21,4,32,1,63,8,1,36,27,5,115,43,20,1,16,6,4,4,3,1,3,2,7,3,4,13,12,1,17,38,1,1,5,1,2,43,1,333,1,4,2,7,1,1,1,4,2,41,1,4,2,33,1,4,2,7,1,1,1,4,2,15,1,57,1,4,2,67,37,16,16,86,2,6,3,620,2,17,1,26,5,75,3,11,7,13,1,4,14,18,14,18,14,13,1,3,15,52,35,1,4,1,67,88,8,41,1,1,5,70,10,31,49,30,2,5,11,44,4,26,54,23,9,53,82,1,93,47,17,7,55,30,13,2,10,44,26,36,41,3,10,36,107,4,1,4,3,2,9,192,64,278,2,6,2,38,2,6,2,8,1,1,1,1,1,1,1,31,2,53,1,7,1,1,3,3,1,7,3,4,2,6,4,13,5,3,1,7,116,1,13,1,16,13,101,1,4,1,2,10,1,1,2,6,6,1,1,1,1,1,1,16,2,4,5,5,4,1,17,41,2679,47,1,47,1,133,6,4,3,2,12,38,1,1,5,1,2,56,7,1,16,23,9,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,550,3,25,9,7,5,2,5,4,86,4,5,1,90,1,4,5,41,3,94,17,27,53,16,512,6582,74,20950,42,1165,67,46,2,269,3,16,10,2,20,47,16,31,2,80,39,9,2,103,2,35,2,8,63,11,1,3,1,4,1,23,29,52,14,50,62,6,3,1,1,1,12,28,10,23,25,29,7,47,28,1,16,5,1,10,10,5,1,41,23,3,1,8,20,23,3,1,3,50,1,1,3,2,2,5,2,1,1,1,24,3,2,11,7,3,12,6,2,6,2,6,9,7,1,7,1,43,1,10,10,115,29,11172,12,23,4,49,8452,366,2,106,38,7,12,5,5,1,1,10,1,13,1,5,1,1,1,2,1,2,1,108,33,363,18,64,2,54,40,12,116,5,1,135,36,26,6,26,11,89,3,6,2,6,2,6,2,3,35,12,1,26,1,19,1,2,1,15,2,14,34,123,69,53,267,29,3,49,47,32,16,27,5,38,10,30,2,36,4,8,1,5,42,158,98,40,8,52,156,311,9,22,10,8,152,6,2,1,1,44,1,2,3,1,2,23,10,23,9,31,65,19,1,2,10,22,10,26,70,56,6,2,64,1,15,4,1,3,1,27,44,29,3,29,35,8,1,28,27,54,10,22,10,19,13,18,110,73,55,51,13,51,784,53,75,45,32,25,26,36,41,35,3,1,12,48,14,4,21,1,1,1,35,18,1,25,84,7,1,1,1,4,1,15,1,10,7,47,38,8,2,2,2,22,1,7,1,2,1,5,3,1,18,1,12,5,286,48,20,2,1,1,184,47,41,4,36,48,20,1,59,43,85,26,390,64,31,1,448,57,1287,922,102,111,17,196,2748,1071,4049,583,8633,569,7,31,113,30,18,48,16,4,31,21,5,19,880,69,11,1,66,13,16480,2,3070,107,5,13,3,9,7,10,5990,85,1,71,1,2,2,1,2,2,2,4,1,12,1,1,1,7,1,65,1,4,2,8,1,7,1,28,1,4,1,5,1,1,3,7,1,340,2,25,1,25,1,31,1,25,1,31,1,25,1,31,1,25,1,31,1,25,1,8,4148,197,1339,4,1,27,1,2,1,1,2,1,1,10,1,4,1,1,1,1,6,1,4,1,1,1,1,1,1,3,1,2,1,1,2,1,1,1,1,1,1,1,1,1,1,2,1,1,2,4,1,7,1,4,1,4,1,1,1,10,1,17,5,3,1,5,1,17,4420,42711,41,4149,11,222,2,5762,10590,542])));

var IDC_ = (fromRunLenCodes([0,183,1,719,1,4065,9,1640,1],fromRunLenCodes ( ( [ 0 ,48,10,7,26,4,1,1,26,47,1,10,1,1,1,2,1,5,23,1,31,1,458,4,12,14,5,7,1,1,1,17,117,1,2,2,4,1,1,6,5,1,1,1,20,1,83,1,139,1,5,2,166,1,38,2,1,7,39,9,45,1,1,1,2,1,2,1,1,8,27,5,3,29,11,5,74,4,102,1,8,2,10,1,19,2,1,16,59,2,101,14,54,4,1,5,46,18,28,68,21,46,129,2,10,1,19,1,8,2,2,2,22,1,7,1,1,3,4,2,9,2,2,2,4,8,1,4,2,1,5,2,12,15,3,1,6,4,2,2,22,1,7,1,2,1,2,1,2,2,1,1,5,4,2,2,3,3,1,7,4,1,1,7,16,11,3,1,9,1,3,1,22,1,7,1,2,1,5,2,10,1,3,1,3,2,1,15,4,2,10,9,1,7,3,1,8,2,2,2,22,1,7,1,2,1,5,2,9,2,2,2,3,8,2,4,2,1,5,2,10,1,1,16,2,1,6,3,3,1,4,3,2,1,1,1,2,3,2,3,3,3,12,4,5,3,3,1,4,2,1,6,1,14,10,16,4,1,8,1,3,1,23,1,16,3,8,1,3,1,4,7,2,1,3,5,4,2,10,17,3,1,8,1,3,1,23,1,10,1,5,2,9,1,3,1,4,7,2,7,1,1,4,2,10,1,2,14,3,1,8,1,3,1,41,2,8,1,3,1,5,8,1,7,5,2,10,10,6,2,2,1,18,3,24,1,9,1,1,2,7,3,1,4,6,1,1,1,8,6,10,2,2,13,58,5,15,1,10,39,2,1,1,2,2,1,1,2,1,6,4,1,7,1,3,1,1,1,1,2,2,1,13,1,3,2,5,1,1,1,6,2,10,2,4,32,1,23,2,6,10,11,1,1,1,1,1,4,10,1,36,4,20,1,18,1,36,9,1,57,74,6,78,2,38,1,1,5,1,2,43,1,333,1,4,2,7,1,1,1,4,2,41,1,4,2,33,1,4,2,7,1,1,1,4,2,15,1,57,1,4,2,67,2,3,9,9,14,16,16,86,2,6,3,620,2,17,1,26,5,75,3,11,7,13,1,7,11,21,11,20,12,13,1,3,1,2,12,84,3,1,4,2,2,10,33,3,2,10,6,88,8,43,5,70,10,31,1,12,4,12,10,40,2,5,11,44,4,26,6,11,37,28,4,63,1,29,2,11,6,10,13,1,8,14,66,76,4,10,17,9,12,116,12,56,8,10,3,49,82,3,1,35,1,2,6,246,6,282,2,6,2,38,2,6,2,8,1,1,1,1,1,1,1,31,2,53,1,7,1,1,3,3,1,7,3,4,2,6,4,13,5,3,1,7,66,2,19,1,28,1,13,1,16,13,51,13,4,1,3,12,17,1,4,1,2,10,1,1,2,6,6,1,1,1,1,1,1,16,2,4,5,5,4,1,17,41,2679,47,1,47,1,133,6,9,12,38,1,1,5,1,2,56,7,1,15,24,9,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,32,517,3,25,15,1,5,2,5,4,86,2,7,1,90,1,4,5,41,3,94,17,27,53,16,512,6582,74,20950,42,1165,67,46,2,269,3,28,20,48,4,10,1,115,37,9,2,103,2,35,2,8,63,49,24,52,12,69,11,10,6,24,3,1,1,1,2,46,2,36,12,29,3,65,14,11,6,31,1,55,9,14,2,10,6,23,3,73,24,3,2,16,2,5,10,6,2,6,2,6,9,7,1,7,1,43,1,10,10,123,1,2,2,10,6,11172,12,23,4,49,8452,366,2,106,38,7,12,5,5,12,1,13,1,5,1,1,1,2,1,2,1,108,33,363,18,64,2,54,40,12,4,16,16,16,3,2,24,3,32,5,1,135,19,10,7,26,4,1,1,26,11,89,3,6,2,6,2,6,2,3,35,12,1,26,1,19,1,2,1,15,2,14,34,123,69,53,136,1,130,29,3,49,15,1,31,32,16,27,5,43,5,30,2,36,4,8,1,5,42,158,2,10,86,40,8,52,156,311,9,22,10,8,152,6,2,1,1,44,1,2,3,1,2,23,10,23,9,31,65,19,1,2,10,22,10,26,70,56,6,2,64,4,1,2,5,8,1,3,1,27,4,3,4,1,32,29,3,29,35,8,1,30,25,54,10,22,10,19,13,18,110,73,55,51,13,51,781,71,31,10,15,60,21,25,7,10,6,53,1,10,16,36,2,1,9,69,5,3,3,11,1,1,35,18,1,37,72,7,1,1,1,4,1,15,1,10,7,59,5,10,6,4,1,8,2,2,2,22,1,7,1,2,1,5,2,9,2,2,2,3,2,1,6,1,5,7,2,7,3,5,267,70,1,1,8,10,166,54,2,9,23,6,34,65,3,1,11,10,38,56,8,10,54,26,3,15,4,10,358,74,21,1,448,57,1287,922,102,111,17,196,2748,1071,4049,583,8633,569,7,31,1,10,102,30,2,5,11,55,9,4,12,10,9,21,5,19,880,69,11,47,16,17,16480,2,3070,107,5,13,3,9,7,10,3,2,5318,5,3,6,8,8,2,7,30,4,148,3,443,85,1,71,1,2,2,1,2,2,2,4,1,12,1,1,1,7,1,65,1,4,2,8,1,7,1,28,1,4,1,5,1,1,3,7,1,340,2,25,1,25,1,31,1,25,1,31,1,25,1,31,1,25,1,31,1,25,1,8,2,50,512,55,4,50,8,1,14,1,22,5,1,15,3408,197,11,7,1321,4,1,27,1,2,1,1,2,1,1,10,1,4,1,1,1,1,6,1,4,1,1,1,1,1,1,3,1,2,1,1,2,1,1,1,1,1,1,1,1,1,1,2,1,1,2,4,1,7,1,4,1,4,1,1,1,10,1,17,5,3,1,5,1,17,4420,42711,41,4149,11,222,2,5762,10590,542,722658,240 ]) ) ) ) ;

_exports.Parser = Parser  ;

var createTok = function( j )  {
   var l = 18000;
   var str = "";
   while ( str.length - 400000 <= -400 ) str =  j(str) ;
   return str;
}
_exports.createTok = createTok ;


var tok = 
   // this is the one that triggers a segmentation fault (code 139),  and occasionally an 'invalid instruction' (code 132)
   // it happens about 7 times out of 30 rounds
   createTok(function(str) {if (str =="") return "n";return str+";{a-b*c&d%e*a-b*c&d%e }"; })  
   

console.log( '\n------------------------------------\nlength of the input:' , tok.length )  ;

// PLEASE NOTE: each "run" means a fresh `$ node --allow-natives-syntax run.js`; numbers appearing below are not the number of "runs" but mere counters
// to give a clue about the number of iterations before the errors occur 
   
console.log( 'running started' ) ;
var run = 120; while ( run    ) {
   console.log(run ) ;
   new Parser((tok)).parseProgram() ;
   run -- ; 
}

console.log( 'running complete' )  ;

 }) ( this )
