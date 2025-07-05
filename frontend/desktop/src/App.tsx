import { Box, CssBaseline, ThemeProvider, createTheme, Toolbar, Typography, AppBar } from '@mui/material';
import { LimsStageSystemWrapper } from './components/LimsStageSystemWrapper';
import { LimsChatMessage } from './types/stage';

const theme = createTheme({
  palette: {
    mode: 'dark',
    primary: {
      main: '#2196f3',
    },
    secondary: {
      main: '#f50057',
    },
    background: {
      default: '#121212',
      paper: '#1e1e1e',
    },
  },
});

function App() {
  const handleChatMessage = (message: LimsChatMessage) => {
    console.log('Chat message received:', message);
  // The LimsStageSystemWrapper manages its own chat state and TLA+ compliance
  };

  return (
    <ThemeProvider theme={theme}>
      <CssBaseline />
      <Box sx={{ display: 'flex', flexDirection: 'column', height: '100vh' }}>
        <AppBar position="static">
          <Toolbar>
            <Typography variant="h6" component="div" sx={{ flexGrow: 1 }}>
              ALIMS - TLA+-Verified Laboratory Information Management System
            </Typography>
          </Toolbar>
        </AppBar>
        <Box sx={{ flexGrow: 1, overflow: 'hidden' }}>
          <LimsStageSystemWrapper
            onChatMessage={handleChatMessage}
          />
        </Box>
      </Box>
    </ThemeProvider>
  );
}

export default App;
