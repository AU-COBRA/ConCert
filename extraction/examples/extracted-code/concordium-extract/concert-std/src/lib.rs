pub use concert_std_derive::*;
use immutable_map::TreeMap;

use std::marker::PhantomData;
use concordium_std::{AccountAddress, Address, ContractAddress, Cursor, Deserial, ParseError, ParseResult, Read, Serial, Write};

pub struct SerializedValue<'a>(&'a Vec<u8>);

#[derive(Clone, Copy)]
pub enum ActionBody<'a> {
    Transfer(Address, i64),
    Call(Address, i64, &'a SerializedValue<'a>),
}

pub trait ConCertDeserial<'a>: Sized {
    fn concert_deserial<R: Read>(source: &mut R, arena: &'a bumpalo::Bump) -> ParseResult<Self>;
}

pub trait ConCertSerial {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err>;
}

impl<'a, X: ConCertSerial> ConCertSerial for &'a X {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        (*self).concert_serial(out)
    }
}

impl<'a, X: ConCertDeserial<'a>> ConCertDeserial<'a> for &'a X {
    fn concert_deserial<R: Read>(source: &mut R, arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        let x: X = ConCertDeserial::concert_deserial(source, arena)?;
        Ok(arena.alloc(x))
    }
}

impl<A: ?Sized> ConCertSerial for PhantomData<A> {
    fn concert_serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        Ok(())
    }
}

impl<'a, A: ?Sized> ConCertDeserial<'a> for PhantomData<A> {
    fn concert_deserial<R: Read>(_source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        Ok(PhantomData)
    }
}

impl ConCertSerial for () {
    fn concert_serial<W: Write>(&self, _out: &mut W) -> Result<(), W::Err> {
        Ok(())
    }
}

impl<'a> ConCertDeserial<'a> for () {
    fn concert_deserial<R: Read>(_source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        Ok(())
    }
}

impl<A: ConCertSerial, B: ConCertSerial> ConCertSerial for (A, B) {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.0.concert_serial(out)?;
        self.1.concert_serial(out)
    }
}

impl<'a, A: ConCertDeserial<'a>, B: ConCertDeserial<'a>> ConCertDeserial<'a> for (A, B) {
    fn concert_deserial<R: Read>(source: &mut R, arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        let x = A::concert_deserial(source, arena)?;
        let y = B::concert_deserial(source, arena)?;
        Ok((x, y))
    }
}

impl ConCertSerial for bool {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.serial(out)
    }
}

impl<'a> ConCertDeserial<'a> for bool {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        Self::deserial(source)
    }
}

impl ConCertSerial for u8 {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u8(*self)
    }
}

impl<'a> ConCertDeserial<'a> for u8 {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        source.read_u8()
    }
}

impl ConCertSerial for u16 {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u16(*self)
    }
}

impl<'a> ConCertDeserial<'a> for u16 {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        source.read_u16()
    }
}

impl ConCertSerial for u32 {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u32(*self)
    }
}

impl<'a> ConCertDeserial<'a> for u32 {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        source.read_u32()
    }
}

impl ConCertSerial for u64 {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_u64(*self)
    }
}

impl<'a> ConCertDeserial<'a> for u64 {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        source.read_u64()
    }
}

impl ConCertSerial for i8 {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_i8(*self)
    }
}

impl<'a> ConCertDeserial<'a> for i8 {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        source.read_i8()
    }
}

impl ConCertSerial for i16 {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_i16(*self)
    }
}

impl<'a> ConCertDeserial<'a> for i16 {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        source.read_i16()
    }
}

impl ConCertSerial for i32 {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_i32(*self)
    }
}

impl<'a> ConCertDeserial<'a> for i32 {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        source.read_i32()
    }
}

impl ConCertSerial for i64 {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        out.write_i64(*self)
    }
}

impl<'a> ConCertDeserial<'a> for i64 {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        source.read_i64()
    }
}

impl<A: ConCertSerial> ConCertSerial for Option<A> {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        match self {
            None => 0u8.concert_serial(out),
            Some(a) => {
                1u8.concert_serial(out)?;
                a.concert_serial(out)
            }
        }
    }
}

impl<'a, A: ConCertDeserial<'a>> ConCertDeserial<'a> for Option<A> {
    fn concert_deserial<R: Read>(source: &mut R, arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        let u = u8::concert_deserial(source, arena)?;
        match u {
            0 => Ok(None),
            1 => {
                let a = A::concert_deserial(source, arena)?;
                Ok(Some(a))
            },
            _ => Err(ParseError::default())
        }
    }
}

impl ConCertSerial for String {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.serial(out)
    }
}

impl<'a> ConCertDeserial<'a> for String {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        Self::deserial(source)
    }
}

impl<K: ConCertSerial, V: ConCertSerial> ConCertSerial for TreeMap<K, V> {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        let len = self.len() as u32;
        len.concert_serial(out)?;
        for (k, v) in self.iter() {
            k.concert_serial(out)?;
            v.concert_serial(out)?;
        }
        Ok(())
    }
}

impl<'a, K: Ord + Clone + ConCertDeserial<'a>, V: Clone + ConCertDeserial<'a>> ConCertDeserial<'a> for TreeMap<K, V> {
    fn concert_deserial<R: Read>(source: &mut R, arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        let len = u32::concert_deserial(source, arena)?;
        let mut map = TreeMap::new();
        for _ in 0..len {
            let k = K::concert_deserial(source, arena)?;
            let v = V::concert_deserial(source, arena)?;
            map = map.insert(k, v);
        }
        Ok(map)
    }
}

impl ConCertSerial for AccountAddress {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.serial(out)
    }
}

impl<'a> ConCertDeserial<'a> for AccountAddress {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        Self::deserial(source)
    }
}

impl ConCertSerial for ContractAddress {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.serial(out)
    }
}

impl<'a> ConCertDeserial<'a> for ContractAddress {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        Self::deserial(source)
    }
}

impl ConCertSerial for Address {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.serial(out)
    }
}

impl<'a> ConCertDeserial<'a> for Address {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        Self::deserial(source)
    }
}

impl<'a> ConCertSerial for SerializedValue<'a> {
    fn concert_serial<W: Write>(&self, out: &mut W) -> Result<(), W::Err> {
        self.0.serial(out)
    }
}

impl<'a> ConCertDeserial<'a> for SerializedValue<'a> {
    fn concert_deserial<R: Read>(source: &mut R, _arena: &'a bumpalo::Bump) -> ParseResult<Self> {
        let v = <_>::deserial(source)?;
        Ok(SerializedValue(_arena.alloc(v)))
    }
}

pub fn to_bytes<S: ConCertSerial>(x: &S) -> Vec<u8> {
    let mut out = Vec::new();
    let mut cursor = Cursor::new(&mut out);
    x.concert_serial(&mut cursor).expect("Writing to a vector should succeed.");
    out
}
