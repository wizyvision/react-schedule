import { TableCell, TableContainer, Box } from '@mui/material';
import { styled } from '@mui/system';

const StyledTableContainer = styled(TableContainer)({
  width: '100%',
  height: '100%',
  maxHeight: 700,
  maxWidth: '-webkit-fill-available',
  position: 'relative',
  border: '1px solid rgba(0,0,0,0.12)',
  backgroundColor: '#FFFFFF',
  overflow: 'auto',
});

const StickyCell = styled(TableCell)({
  left: 0,
  position: 'sticky',
  zIndex: 900,
  backgroundColor: 'white',
  minWidth: 200,
  padding: 0,
  borderRight: '2px solid rgba(0,0,0,0.2)',
});

const ResourceCell = styled(Box)({
  border: 'none',
  width: 200,
  paddingLeft: 8,
  paddingRight: 8
});

const StyledBox = styled(Box)({
  display: 'flex',
  alignItems: 'center',
})

const TimeSlots = styled(TableCell)({
  textAlign: 'left',
  backgroundColor: '#FFFFFF',
  borderRight: '1px solid  rgba(0,0,0,0.05)',
  fontSize: '14px',
  fontWeight: '600',
  
});

export { StyledTableContainer, StickyCell, ResourceCell, StyledBox, TimeSlots };
