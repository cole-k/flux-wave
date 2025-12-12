use crate::{
    path_resolution::resolve_path,
    rvec::RVec,
    tcb::{
        misc::{empty_netlist, get_homedir_fd, string_to_rvec_u8},
        path::{HostPathSafe, HostPath},
    },
    types::*,
};
use flux_rs::*;
use RuntimeError::*;

#[alias(type FitsBool(buf: int, cnt: int) = bool[fits_in_lin_mem(buf, cnt)])]
pub type FitsBool = bool;

#[alias(type FitsUsize(buf: int) = usize{cnt : fits_in_lin_mem(buf, cnt)})]
pub type FitsUsize = usize;

//#[ensures(safe(&result))]
// #[with_ghost_var(trace: &mut Trace)]
// #[external_methods(init_std_fds, unwrap, as_raw_fd, create, to_owned, clone)]
// #[external_calls(open, forget, get_homedir_fd, from)]
pub fn fresh_ctx(homedir: String) -> VmCtx {
    let memlen = LINEAR_MEM_SIZE;
    // let mem = vec![0; memlen];
    let mem = RVec::from_elem_n(0, memlen);

    let mut fdmap = FdMap::new();
    let _ = fdmap.init_std_fds();
    let homedir_host_fd = get_homedir_fd(&homedir) as usize;
    // let homedir_file = std::fs::File::open(&homedir).unwrap();
    // let homedir_fd = homedir_file.as_raw_fd();
    if homedir_host_fd >= 0 {
        let _ = fdmap.create(HostFd::from_raw(homedir_host_fd));
    }
    // Need to forget file to make sure it does not get auto-closed
    // when it gets out of scope
    // std::mem::forget(homedir_file);
    // let log_path = "".to_owned();
    // let log_path = String::new();

    let arg_buffer = RVec::new();
    let argc = 0;
    let env_buffer = RVec::new();
    let envc = 0;

    let netlist = empty_netlist();
    VmCtx {
        ghost_raw: 100, //
        mem,
        memlen,
        fdmap,
        homedir,
        homedir_host_fd: HostFd::from_raw(homedir_host_fd),
        // errno: Success,
        arg_buffer,
        argc,
        env_buffer,
        envc,
        // log_path,
        netlist,
    }
}

impl VmCtx {
    /// Check whether sandbox pointer is actually inside the sandbox
    // TODO: can I eliminate this in favor os in_lin_mem_usize?
    #[vars(
        $wk0(ctx, ptr) = [true];
        $wk1(v, ctx, ptr) = [v == (0 <= ptr && ptr < LINEAR_MEM_SIZE)];
    )]
    #[sig(fn(&VmCtx[@ctx], ptr:SboxPtr) -> bool[#v]
          requires $wk0(ctx, ptr)
          ensures $wk1(v, ctx, ptr)
    )]
    pub fn in_lin_mem(&self, ptr: SboxPtr) -> bool {
        (ptr as usize >= 0) && (ptr as usize) < self.memlen
    }

    #[vars(
        $wk0(ctx, ptr) = [true];
        $wk1(v, ctx, ptr) = [v == (0 <= ptr && ptr < LINEAR_MEM_SIZE)];
    )]
    #[sig(fn(&VmCtx[@ctx], ptr:usize) -> bool[#v]
          requires $wk0(ctx, ptr)
          ensures $wk1(v, ctx, ptr)
    )]
    pub fn in_lin_mem_usize(&self, ptr: usize) -> bool {
        ptr >= 0 && ptr < self.memlen
    }

    /// Check whether buffer is entirely within sandbox
    // Can I eliminate this in favor of fits_in_lin_mem_usize
    // #[vars(
    //     $wk0(ctx, buf, cnt) = [true];
    //     $wk1(v, ctx, buf, cnt) = [fits_in_lin_mem(buf, cnt)];
    // )]
    // #[sig(fn(&VmCtx[@ctx], buf: SboxPtr, cnt:u32) -> bool[#v]
    //       requires $wk0(ctx, buf, cnt)
    //       ensures $wk1(v, ctx, buf, cnt)
    // )]
    #[sig(fn(&VmCtx[@ctx], buf: SboxPtr, cnt:u32) -> bool[fits_in_lin_mem(buf, cnt)])]
    pub fn fits_in_lin_mem(&self, buf: SboxPtr, cnt: u32) -> bool {
        let total_size = (buf as usize) + (cnt as usize);
        if total_size >= self.memlen {
            return false;
        }
        self.in_lin_mem(buf) && self.in_lin_mem(cnt) && buf <= buf + cnt
    }

    // #[vars(
    //     $wk0(ctx, buf, cnt) = [true];
    //     $wk1(v, ctx, buf, cnt) = [fits_in_lin_mem(buf, cnt)];
    // )]
    // #[sig(fn(&VmCtx[@ctx], buf: usize, cnt:usize) -> bool[#v]
    //       requires $wk0(ctx, buf, cnt)
    //       ensures $wk1(v, ctx, buf, cnt)
    // )]
    #[sig(fn(&VmCtx[@ctx], buf: usize, cnt:usize) -> bool[fits_in_lin_mem(buf, cnt)])]
    pub fn fits_in_lin_mem_usize(&self, buf: usize, cnt: usize) -> bool {
        let total_size = buf + cnt;
        if total_size >= self.memlen {
            return false;
        }
        self.in_lin_mem_usize(buf) && self.in_lin_mem_usize(cnt) && buf <= buf + cnt
    }

    /// Copy buffer from sandbox to host
    #[vars(
        $wk0(ctx, src, n) = [0 <= n, src + n < LINEAR_MEM_SIZE];
        $wk1(v, ctx, src, n) = [v == n];
    )]
    #[sig(fn(&VmCtx[@ctx], src:SboxPtr, n:u32) -> RVec<u8>[#v]
          requires $wk0(ctx, src, n)
          ensures $wk1(v, ctx, src, n)
    )]
    pub fn copy_buf_from_sandbox(&self, src: SboxPtr, n: u32) -> RVec<u8> {
        let mut host_buffer: RVec<u8> = RVec::from_elem_n(0, n as usize);
        // FLUX-TODO2: capacity: host_buffer.reserve_exact(n as usize);
        // assert!(src >= 0);
        // assert!(((n as usize) < self.memlen) && ((n as usize) >= 0));
        self.memcpy_from_sandbox(&mut host_buffer, src, n);
        host_buffer
    }

    /// Copy buffer from from host to sandbox
    #[sig(fn(self: &mut VmCtx[@dummy], SboxPtr, &RVec<u8>, u32) -> Result<(), RuntimeError>)]
    pub fn copy_buf_to_sandbox(
        &mut self,
        dst: SboxPtr,
        src: &RVec<u8>,
        n: u32,
    ) -> Result<(), RuntimeError> {
        if src.len() < n as usize || !self.fits_in_lin_mem(dst, n) {
            return Err(Efault);
        }
        self.memcpy_to_sandbox(dst, src, n);
        Ok(())
    }

    /// Copy arg buffer from from host to sandbox
    #[vars(
        $wk0(ctx, dst, n) = [ctx.arg_buf == n];
    )]
    #[sig(fn(&mut VmCtx[@ctx], dst:SboxPtr, n:u32) -> Result<(), RuntimeError>
          requires $wk0(ctx, dst, n)
    )]
    pub fn copy_arg_buffer_to_sandbox(&mut self, dst: SboxPtr, n: u32) -> Result<(), RuntimeError> {
        if !self.fits_in_lin_mem(dst, n) {
            return Err(Efault);
        }
        let arg_buffer = &self.arg_buffer.clone();
        self.memcpy_to_sandbox(dst, &arg_buffer, n);
        Ok(())
    }

    /// Copy arg buffer from from host to sandbox
    #[vars(
        $wk0(ctx, dst, n) = [ctx.arg_buf == n];
    )]
    #[sig(fn(&mut VmCtx[@ctx], dst:SboxPtr, n:u32) -> Result<(), RuntimeError>
          requires $wk0(ctx, dst, n)
    )]
    pub fn copy_environ_buffer_to_sandbox(
        &mut self,
        dst: SboxPtr,
        n: u32,
    ) -> Result<(), RuntimeError> {
        if !self.fits_in_lin_mem(dst, n) {
            return Err(Efault);
        }
        let env_buffer = &self.env_buffer.clone();
        self.memcpy_to_sandbox(dst, &env_buffer, n);
        Ok(())
    }

    #[vars(
        $wk0(ctx, sbx, n, should_follow, hostfd) = [true];
        $wk1(v, ctx, sbx, n, should_follow, hostfd) = [
            v.depth >= 0,
            v.is_relative,
            (should_follow => v.non_symlink),
            v.non_symlink_prefixes
        ];
    )]
    #[sig(fn(&VmCtx[@ctx], sbx:SboxPtr, n:u32, should_follow:bool, hostfd:HostFd)
             -> Result<HostPath{v: $wk1(v, ctx, sbx, n, should_follow, hostfd)}, RuntimeError>
          requires $wk0(ctx, sbx, n, should_follow, hostfd)
    )]
    pub fn translate_path(
        &self,
        path: SboxPtr,
        path_len: u32,
        should_follow: bool,
        dirfd: HostFd,
    ) -> Result<HostPath, RuntimeError> {
        if !self.fits_in_lin_mem(path, path_len) {
            return Err(Eoverflow);
        }
        let host_buffer = self.copy_buf_from_sandbox(path, path_len);
        resolve_path(host_buffer, should_follow, dirfd)
        // self.resolve_path(host_buffer)
    }

    pub fn get_homedir(&self) -> RVec<u8> {
        string_to_rvec_u8(&self.homedir)
        // self.homedir.as_bytes().to_vec()
    }

    #[vars(
        $wk0(ctx, cnt) = [fits_in_lin_mem(2, cnt)];
        $wk1(v, ctx, cnt) = [true];
    )]
    #[sig(fn(&VmCtx[@ctx], cnt:usize) -> u16[#v]
          requires $wk0(ctx, cnt)
          ensures  $wk1(v, ctx, cnt)
    )]
    pub fn read_u16(&self, start: usize) -> u16 {
        let bytes: [u8; 2] = [self.mem[start], self.mem[start + 1]];
        u16::from_le_bytes(bytes)
    }

    /// read u32 from wasm linear memory
    // Not thrilled about this implementation, but it works
    #[vars(
        $wk0(ctx, cnt) = [fits_in_lin_mem(4, cnt)];
        $wk1(v, ctx, cnt) = [true];
    )]
    #[sig(fn(&VmCtx[@ctx], cnt:usize) -> u32[#v]
          requires $wk0(ctx, cnt)
          ensures  $wk1(v, ctx, cnt)
    )]
    pub fn read_u32(&self, start: usize) -> u32 {
        let bytes: [u8; 4] = [
            self.mem[start],
            self.mem[start + 1],
            self.mem[start + 2],
            self.mem[start + 3],
        ];
        u32::from_le_bytes(bytes)
    }

    /// read u64 from wasm linear memory
    // Not thrilled about this implementation, but it works
    // TODO: need to test different implementatiosn for this function
    #[vars(
        $wk0(ctx, cnt) = [fits_in_lin_mem(8, cnt)];
        $wk1(v, ctx, cnt) = [true];
    )]
    #[sig(fn(&VmCtx[@ctx], cnt:usize) -> u64[#v]
          requires $wk0(ctx, cnt)
          ensures  $wk1(v, ctx, cnt)
    )]
    pub fn read_u64(&self, start: usize) -> u64 {
        let bytes: [u8; 8] = [
            self.mem[start],
            self.mem[start + 1],
            self.mem[start + 2],
            self.mem[start + 3],
            self.mem[start + 4],
            self.mem[start + 5],
            self.mem[start + 6],
            self.mem[start + 7],
        ];
        u64::from_le_bytes(bytes)
    }

    /// read (u32,u32) from wasm linear memory
    pub fn read_u32_pair(&self, start: usize) -> RuntimeResult<(u32, u32)> {
        if !self.fits_in_lin_mem_usize(start, 8) {
            return Err(Eoverflow);
        }
        let x1 = self.read_u32(start);
        let x2 = self.read_u32(start + 4);
        // Ok(Pair { fst: x1, snd: x2 })
        Ok((x1, x2))
    }

    // TODO @cx is redundant here but due to https://github.com/liquid-rust/flux/issues/158
    #[vars(
        $wk0(ctx, cnt, v) = [fits_in_lin_mem(1, cnt)];
    )]
    #[sig(fn(&mut VmCtx[@ctx], cnt:usize, v: u8)
          requires $wk0(ctx, cnt, v)
    )]
    pub fn write_u8(&mut self, offset: usize, v: u8) {
        self.mem[offset] = v;
    }

    /// write u16 to wasm linear memory
    // Not thrilled about this implementation, but it works
    // #[with_ghost_var(trace: &mut Trace)]
    // #[external_methods(to_le_bytes)]
    // #[requires(self.fits_in_lin_mem_usize(start, 2, trace))]
    // #[requires(ctx_safe(self))]
    // #[requires(trace_safe(trace, self))]
    // #[ensures(ctx_safe(self))]
    // #[ensures(trace_safe(trace, self))]
    // // #[ensures(effects!(old(trace), trace, effect!(WriteMem, addr, 2) if addr == start as usize))]
    #[vars(
        $wk0(ctx, cnt, v) = [fits_in_lin_mem(2, cnt)];
    )]
    #[sig(fn(&mut VmCtx[@ctx], cnt:usize, v: u16)
          requires $wk0(ctx, cnt, v)
    )]
    pub fn write_u16(&mut self, start: usize, v: u16) {
        let bytes: [u8; 2] = v.to_le_bytes();
        self.write_u8(start, bytes[0]);
        self.write_u8(start + 1, bytes[1]);
    }

    /// write u32 to wasm linear memory
    // Not thrilled about this implementation, but it works
    // #[with_ghost_var(trace: &mut Trace)]
    // #[external_methods(to_le_bytes)]
    // #[requires(self.fits_in_lin_mem_usize(start, 4, trace))]
    // #[requires(ctx_safe(self))]
    // #[requires(trace_safe(trace, self))]
    // #[ensures(ctx_safe(self))]
    // #[ensures(trace_safe(trace, self))]
    // // #[ensures(effects!(old(trace), trace, effect!(WriteMem, addr, 4) if addr == start as usize))]
    #[vars(
        $wk0(ctx, cnt, v) = [fits_in_lin_mem(4, cnt)];
    )]
    #[sig(fn(&mut VmCtx[@ctx], cnt:usize, v: u32)
          requires $wk0(ctx, cnt, v)
    )]
    pub fn write_u32(&mut self, start: usize, v: u32) {
        let bytes: [u8; 4] = v.to_le_bytes();
        self.write_u8(start, bytes[0]);
        self.write_u8(start + 1, bytes[1]);
        self.write_u8(start + 2, bytes[2]);
        self.write_u8(start + 3, bytes[3]);
    }

    // TODO: replace with faster raw ptr memread/memwrite
    // #[with_ghost_var(trace: &mut Trace)]
    // #[external_methods(to_le_bytes)]
    // #[requires(self.fits_in_lin_mem_usize(start, 8, trace))]
    // #[requires(ctx_safe(self))]
    // #[requires(trace_safe(trace, self))]
    // #[ensures(ctx_safe(self))]
    // #[ensures(trace_safe(trace, self))]
    // // #[ensures(effects!(old(trace), trace, effect!(WriteMem, addr, 8) if addr == start as usize))]
    #[vars(
        $wk0(ctx, cnt, v) = [fits_in_lin_mem(8, cnt)];
    )]
    #[sig(fn(&mut VmCtx[@ctx], cnt:usize, v: u64)
          requires $wk0(ctx, cnt, v)
    )]
    pub fn write_u64(&mut self, start: usize, v: u64) {
        let bytes: [u8; 8] = v.to_le_bytes();
        self.write_u8(start, bytes[0]);
        self.write_u8(start + 1, bytes[1]);
        self.write_u8(start + 2, bytes[2]);
        self.write_u8(start + 3, bytes[3]);
        self.write_u8(start + 4, bytes[4]);
        self.write_u8(start + 5, bytes[5]);
        self.write_u8(start + 6, bytes[6]);
        self.write_u8(start + 7, bytes[7]);
    }

    #[qualifiers(MyQ1)]
    #[vars(
        $wk0(ctx, vec) = [true];
        $wk1(v, ctx, vec) = [v.iov_base + v.iov_len <= ctx.base + LINEAR_MEM_SIZE];
    )]
    #[sig(fn(&VmCtx[@ctx], &RVec<WasmIoVec>[@vec]) -> RVec<NativeIoVec{v: $wk1(v, ctx, vec)}>
          requires $wk0(ctx, vec)
    )]
    pub fn translate_iovs(&self, iovs: &RVec<WasmIoVec>) -> RVec<NativeIoVec> {
        let mut idx = 0;
        let mut native_iovs = NativeIoVecs::new();
        let iovcnt = iovs.len();
        while idx < iovcnt {
            let iov = iovs[idx];
            let native_iov = self.translate_iov(iov);
            native_iovs.push(native_iov);
            idx += 1;
        }
        native_iovs
    }
}
