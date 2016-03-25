 ( function(_exports) {
   'use strict'

var Parser = function (src) {

  this.hasL = false;
  this.src = src;
  this.col = 0;
  this.c = 0;
  this.li = 1;
  this.startStmt = false;
  this.foundStmt = false;

  this. ltval = null;
  this. lttype= "";
  this. ltcontents = "" ;
  this.prec = 0 ;
  this. idcontents = "" ; 

  this.li0 = 0;
  this.col0 = 0;
  this.c0 = 0;

};

var _c = function (c) { return c.charCodeAt(0); };

var 
   
    _9 = _c('9'),
    _a = _c('a'),
    _0 = _c('0'), _z = _c('z'),
    _A = _c('A'), __ = _c('_'), _$ = _c('$'), _Z = _c('Z'), _lf = _c('\n'),
    _mul = _c('*'), _ws = _c(' '),
    _cret = _c('\r'),
    _and = _c('&'), _mod = _c(('%')),
   _min = _c(('-'));

var cfFor = 2, cfShortNotValid = 8 , cfNonAssigNotValid = 1, METHD = 1 << 4, cfY = 1 << 8 ;
var cfExpectHeadBePrim = ((1) << ((5))), CFLAGS_PTRN_MEM = cfShortNotValid|cfNonAssigNotValid ; 

var Num,num = Num = function (c) { return (c >= _0 && c <= _9)};
var IDHead = function (c) {
  return (c <= _z && c >= _a) ||
          c === _$ ||
         (c <= _Z && c >= (_A)) ||
          c== ( ( __ ) )
};

var IDBody = function (c) {
  return (c <= _z && c >= _a) ||
          c === _$ ||
         (c <= _Z && c >= (_A)) ||
         (c <= _9 && c >= _0)
};




var lp = Parser.prototype;

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
      case _min: this.opAddMin(peek) ; break;
      case _mul:  
      case _mod: 
         c++ ;
           this.  prec = 0xAD; this.  lttype = 'op'; 
         this.ltcontents = l.slice(this.c,c)  ; 
         this.c=c;
         break ;

      case _and:
          c++ ;
             this.  lttype = 'op' ; this. prec =  0x01D;  this.ltcontents = '&' ;
         this.c=c;
         break ;

      default:

         this.readMisc();
    }
  }

  this.col += ( this.c - start );
};

lp . opAddMin = function(peek) {
        var c = this.c, assig = false, l = this.src ;
        c++ ;
        var r = l.charCodeAt ( c ) ;
        this.ltcontents = this.src.slice(this.c,c)  ;
        this.lttype = assig ? '=' : this.ltcontents ;
        this.c=c;
        this.prec= 0xA7 ; 
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

  return head ;
};

lp.parseNonSeqExpr = function (head, breakIfLessThanThis , cFlags_For ) {
  if (!head) this.err( 'Unexpected ' + this .lttype );
  var n ;
  var _b = null  , _e = null  ; 

  var hasPrefixOrPostfix = false, prec, o, precOrAssocDistance;


  EXPR:
  while (!false) {
    switch (this.lttype) {

      case '-' :
      case 'op' :
         prec = this . prec;
         break ;

      
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

  return this.id();
};

lp.parseExprHead = function (cFlags_For_Sh_Non_Ex ) {
  var head;
  var _c ; 
  var startc, startLoc ;
  var e   ;

  if ( this . lttype == 'Identifier' ) {
      head = this.parseStatementOrID ( cFlags_For_Sh_Non_Ex  ) ; 
      if ( this.foundStmt ) { return head ; } 
  }

  return head ;
} ;

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
