#!/afs/cats.ucsc.edu/courses/cmps112-wm/usr/smalltalk/bin/gst -f
"$Id: charfreq.st,v 1.6 2012-02-23 18:57:46-08 - - $"
"Count frequency of input characters"

nl := Character nl.

Object subclass: BitStream [
   |bitIndex byte myStream|
   BitStream class >> new: fileStream [
      |result|
      result := super new.
      result init: fileStream.
      ^result
   ]
   init: fileStream [
      myStream := fileStream.
      bitIndex := 1.
   ]
   nextBit [
      bitIndex = 1 ifTrue: [
         byte := myStream next.
         bitIndex := 9.
      ].
      bitIndex := bitIndex - 1.
      ^byte value bitAt: bitIndex
   ]
   nextEightBits[
      |eight_bits char|
      eight_bits := 8.
      char := 0.
      [eight_bits ~= 0] whileTrue:[
       |bit bitValue|
       bitValue := 2 raisedTo: eight_bits - 1.
       bit := self nextBit.
       bit = 1
       ifTrue:[char := char + bitValue].
       eight_bits := eight_bits - 1.
      ].
      char = 0
      ifTrue:[|bit|
       bit := self nextBit.
       bit = 0
       ifTrue: [^0]
       ifFalse: [^256]. 
      ]
      ifFalse:[^char].
   ]

   atEnd [
      ^bitIndex = 1 and: [myStream atEnd]
   ]
   currByte [
      ^byte
   ]
]


Object subclass: OutBits [
   |bitIndex currentByte myStream|
   OutBits class >> new [
      self shouldNotImplement.
   ]
   OutBits class >> new: fileStream [
      |result|
      result := super new.
      result init: fileStream.
      ^result
   ]
   clearByte [
      bitIndex := 8.
      currentByte := 0.
   ]
   init: fileStream [
      myStream := fileStream.
      self clearByte.
   ]
   flushByte [
      bitIndex = 8 ifFalse: [
         myStream nextPutByte: currentByte.
         self clearByte.
      ]
   ]
   writeBit: bit [
      currentByte := currentByte bitAt: bitIndex put: bit.
      bitIndex := bitIndex - 1.
      bitIndex = 0 ifTrue: [self flushByte].
   ]
]

writeBitArray := [:outfile :bitCollection|
   |outBytes|
   outBytes := OutBits new: outfile.
   bitCollection do: [:bit| outBytes writeBit: bit].
   outBytes flushByte.
].

Object subclass: Leaf [
   |char count|
   char [ ^ char ]
   count [ ^ count ]

   Leaf class >> new [
      self shouldNotImplement
   ]

   Leaf class >> new: aChar count: aCount [
      |result|
      result := super new.
      result setChar: aChar andCount: aCount.
      ^result
   ]

   setChar: aChar andCount: aCount [
      char := aChar.
      count := aCount.
   ]
   
   isTree [^false]

   <= other [
      ^ (count < other count)
      | ((count = other count) & (char <= other char))
   ]

   printBase: aStream [
      ^ aStream << self class << '(' << char << ',' << count
   ]

   printOn: aStream [
      (self printBase: aStream) << ')'.
   ]

   inorder: visitor prefix: string [
      visitor value: char value: count value: string.
   ]
    
   postorder: bitCollection[
        char ~= 0 & char ~= 256
        ifTrue: [|byteSize|
                  byteSize := 8.
                  bitCollection add: 0.
                  [byteSize ~= 0] whileTrue:[
                      |bit|
                      bit := char bitAt: byteSize.
                      bitCollection add: bit.
                      byteSize := byteSize - 1.
                  ].
                ].

         char = 0
         ifTrue:[|byteSize|
                  byteSize := 10.
                  [byteSize ~= 0] whileTrue:[
                      |bit|
                      bitCollection add: 0.
                      byteSize := byteSize - 1.
                  ].
                ].
          
          char = 256
          ifTrue:[|byteSize|
                  byteSize := 9.
                  [byteSize ~= 0] whileTrue:[
                      |bit|
                      bitCollection add: 0.
                      byteSize := byteSize - 1.
                  ].
                  bitCollection add: 1.
                ].
         ] 
   ]


Leaf subclass: Tree [
   |left right|

   Tree class >> new: aChar count: aCount [
      self shouldNotImplement
   ]

   Tree class >> new: aChar count: aCount left: aLeft right: aRight [
      |result|
      result := super new: aChar count: aCount.
      result setLeft: aLeft andRight: aRight.
      ^ result
   ]

   setLeft: aLeft andRight: aRight [
      left := aLeft.
      right := aRight.
   ]
   
   left [^left]
   right [^right]
   isTree [^true]

   printOn: aStream [
      (self printBase: aStream) << ',' << left << ',' << right << ')'.
   ]

   inorder: visitor prefix: string [
      left inorder: visitor prefix: string, '0'.
      right inorder: visitor prefix: string, '1'.
   ]
   
   postorder: bitCollection[
       left postorder: bitCollection.
       right postorder: bitCollection.
       bitCollection add:1.
       self char = 11
       ifTrue:[bitCollection add:1.].
   ]

]


Character extend [
   isPrint [
      ^ (Character space <= self) & (self <= $~)
   ]
   visible [
      self isPrint ifTrue: [^ '$', self asString]
                   ifFalse: [^ self asInteger printStringRadix: 8]
   ]
]

Object subclass: ZeroArray [
   |theArray|

   ZeroArray class >> new [
      self shouldNotImplement.
   ]

   ZeroArray class >> new: size [
      |result|
      result := super new.
      result init: size.
      ^ result
   ]

   init: size [
      theArray := Array new: size.
   ]

   size [
      ^ theArray size.
   ]

   at: index [
      ^ theArray at: index + 1.
   ]

   at: index put: value [
      ^ theArray at: index + 1 put: value.
   ]

   incr: index [
      (self at: index) isNil
         ifTrue: [ self at: index put: 0].
      self at: index put: (self at: index) + 1.
   ]

   keysAndValuesDo: aBlock [
      (0 to: (self size) - 1) do: [:index |
         aBlock value: index value: (self at: index).
      ]
   ]

]

|args|
args := Smalltalk arguments.

huffmanEncode := [:pqueue|
    |inputfile|
    freqtable := ZeroArray new: 257.
    args size < 2
    ifTrue:[stdout << 'missing argument'. ObjectMemory quit: 0.]
    ifFalse: [|filename|
    filename := args at: 2.
    inputfile := FileStream 
                 open: filename mode: FileStream read
    ].
   [inputfile atEnd not] whileTrue: [
      |ordChar|
     ordChar := inputfile next asInteger.
    freqtable incr: ordChar.
   ].
   freqtable incr: 256.
   inputfile close.
   freqtable keysAndValuesDo: [:key :value |
   (value notNil and: [value > 0]) ifTrue: [
      |newvalue whatchar|
       newvalue := Leaf new: key count: value.
       pqueue add: newvalue.
       ]
    ].
   pqueue size = 1
   ifTrue: [ObjectMemory quit: 0.].
   [pqueue size > 1] whileTrue:[
   |first second new_internal  newcount|
   first := pqueue removeFirst.
   second := pqueue removeFirst.
   first_count := first count.
   second_count := second count.
   newcount := first_count + second_count.
   pqueue size = 0
   ifTrue:[new_internal := Tree 
   new: 11 count: newcount left: first right: second] 
   ifFalse:[new_internal := Tree 
   new: 1 count: newcount left: first right: second]. 
   pqueue add:new_internal.
   ].
].



insertItem := [:bitCollection :item|
      item do:[:bit|
        |intbit|
        intbit := bit asInteger.
        intbit =  48
        ifTrue:[bitCollection add: 0].
        intbit = 49
        ifTrue:[bitCollection add: 1]. 
      ].
].



padWithZeros := [:bitCollection|
    |size zerosToAdd modEight|
    size := bitCollection size.
    modEight := size rem:8.
    zerosToAdd :=  8 - modEight.
    [zerosToAdd ~= 0] whileTrue:[
      bitCollection add:0.
      zerosToAdd := zerosToAdd - 1.
    ].
].

reconstructTree := [:bitStream :stack|
  |bit|
  bit := bitStream nextBit.
  [bit ~= 1 | stack size ~= 1] whileTrue:[
    bit = 0
    ifTrue:[|char leaf|
     char := bitStream nextEightBits.
     char = 1
     ifTrue:[leaf := Leaf new: 256 count: 0]
     ifFalse:[leaf := Leaf new: char count: 0].
     stack add: leaf.
     bit := bitStream nextBit.
    ]
    ifFalse:[
     |first second newinternal|
     second := stack removeLast.
     first  := stack removeLast.
     newinternal := Tree new: 0 count: 0 left: first right: second.  
     stack add: newinternal.
     bit := bitStream nextBit.  
    ]. 
  ].
].

reconstructFile := [:inputStream :outputfile :root|
   |tree_it|
   tree_it := root.
   eof := false.
   [eof = false] whileTrue:[
     |bit|
     bit := inputStream nextBit.
     bit = 0
     ifTrue: [tree_it := tree_it left.]
     ifFalse: [tree_it := tree_it right.].
     tree_it isTree = false
     ifTrue:[
      tree_it char = 256
      ifTrue:[eof := true.]
      ifFalse:[outputfile << tree_it char asCharacter.
      tree_it := root].
     ].  
 ].
].

|option d_option t_option c_option u_option|
option := args at:1.
d_option := '-d'.
t_option := '-t'.
c_option := '-c'.
u_option := '-u'.

option = d_option
ifTrue: [stdout << 'option -d' << nl.].

option = t_option
ifTrue: [|outputfile root pqueue|
         args size = 2
          ifTrue: [outputfile := stdout]
          ifFalse:[|filename|
          filename := args at: 3.
          outputfile := FileStream 
                        open: filename mode: FileStream write]. 
          pqueue := SortedCollection new.
          huffmanEncode value: pqueue.
          root := pqueue removeFirst.
          root inorder: [:char :count :string|
           |whatchar|
           whatchar := char asCharacter.
           outputfile << whatchar visible  
                      << ' ' << count << ' ' << string << nl. 
          ] prefix: ''.
        ].

option = c_option
ifTrue: [|outputfile root hash_code 
          bitCollection inputfilename eofitem pqueue| 
          args size = 2
          ifTrue: [outputfile := stdout]
          ifFalse:[|outputfilename|
          outputfilename := args at: 3.
          outputfile := FileStream 
                        open: outputfilename mode: FileStream write]. 
          pqueue := SortedCollection new.
          huffmanEncode value: pqueue.
          root := pqueue removeFirst.
          bitCollection := OrderedCollection new.
          hash_code := Dictionary new.
          root postorder:bitCollection.
          root inorder: [:char :count :string|
          hash_code at: char put: string.
          ] prefix: ''.
          
          inputfilename := args at: 2. 
          inputfile := FileStream 
                       open: inputfilename mode: FileStream read. 
          inputfile do: [:item| 
          |intitem queryitem|
            intitem :=  item asInteger.
            queryitem := hash_code at: intitem.
            insertItem value: bitCollection value: queryitem.
          ].
          eofitem := hash_code at: 256.
          insertItem value: bitCollection value: eofitem.
          padWithZeros value:bitCollection.
          writeBitArray value:outputfile value:bitCollection.
          outputfile close.
          inputfile close. 
        ].
option = u_option
ifTrue: [|outputfile inputfilename stack root|
        args size = 2
        ifTrue: [outputfile := stdout]
        ifFalse:[|outputfilename|
        outputfilename := args at: 3.
        outputfile := FileStream 
                      open: outputfilename mode: FileStream write]. 
        inputfilename := args at: 2.
        inputfile := FileStream 
                    open: inputfilename mode: FileStream read. 
        inputFileBits := BitStream new: inputfile.
        inputFileBits atEnd = true
        ifTrue:[ObjectMemory quit: 0.].
        stack := OrderedCollection new.
        reconstructTree value: inputFileBits value: stack.
        root := stack removeFirst.
        reconstructFile value: inputFileBits 
                               value: outputfile value: root. 
        outputfile close.
        inputfile close. 
].


"TEST: echo aaaaaaaaaa bbbbb ccc | charfreq.st"
